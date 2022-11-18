/-
Copyright (c) 2021 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
import Std.Tactic.TryThis
import Mathlib.Tactic.Cache
import Mathlib.Tactic.Core
import Mathlib.Tactic.SolveByElim

/-!
# Library search

This file defines a tactic `library_search`
and a term elaborator `library_search%`
that tries to find a lemma
solving the current goal
(subgoals are solved using `solveByElim`).

```
example : x < x + 1 := library_search%
example : Nat := by library_search
```
-/

namespace Mathlib.Tactic.LibrarySearch

open Lean Meta Std.Tactic.TryThis

initialize registerTraceClass `Tactic.librarySearch

-- from Lean.Server.Completion
private def isBlackListed (declName : Name) : MetaM Bool := do
  if declName == ``sorryAx then return false
  if declName matches .str _ "inj" then return false
  if declName matches .str _ "noConfusionType" then return false
  let env ← getEnv
  pure $ declName.isInternal
   || isAuxRecursor env declName
   || isNoConfusion env declName
  <||> isRec declName <||> isMatcher declName

initialize librarySearchLemmas : DeclCache (DiscrTree Name true) ←
  DeclCache.mk "librarySearch: init cache" {} fun name constInfo lemmas => do
    if constInfo.isUnsafe then return lemmas
    if ← isBlackListed name then return lemmas
    withNewMCtxDepth do
      let (_, _, type) ← withReducible <| forallMetaTelescopeReducing constInfo.type
      let keys ← withReducible <| DiscrTree.mkPath type
      pure $ lemmas.insertCore keys name

/-- Shortcut for calling `solveByElimImpl`. -/
def solveByElim (g : MVarId) (depth) := solveByElimImpl false [] depth g

/--
Try to solve the goal either by:
* calling `solveByElim`
* or applying a library lemma then calling  `solveByElim` on the resulting goals.

If it successfully closes the goal, returns `none`.
Otherwise, it returns `some a`, where `a : Array (MetavarContext × List MVarId)`,
with an entry for each library lemma which was successfully applied,
containing the metavariable context after the application, and a list of the subsidiary goals.

(Always succeeds, and the metavariable context stored in the monad is reverted,
unless the goal was completely solved.)

(Note that if `solveByElim` solves some but not all subsidiary goals,
this is not currently tracked.)
-/
def librarySearch (goal : MVarId) (lemmas : DiscrTree Name s) (required : List Expr)
    (solveByElimDepth := 6) : MetaM <| Option (Array <| MetavarContext × List MVarId) := do
  profileitM Exception "librarySearch" (← getOptions) do
  let ty ← goal.getType
  withTraceNode `Tactic.librarySearch (return m!"{exceptOptionEmoji ·} {ty}") do

  let mut suggestions := #[]

  let state0 ← get

  try
    solveByElim goal solveByElimDepth
    if (← checkRequired) then
      return none
    else
      set state0
  catch _ =>
    set state0

  for lem in ← lemmas.getMatch ty do
    trace[Tactic.librarySearch] "{lem}"
    let result ← withTraceNode `Tactic.librarySearch (return m!"{exceptOptionEmoji ·} trying {lem}")
      try
        let newGoals ← goal.apply (← mkConstWithFreshMVarLevels lem)
        (try
          for newGoal in newGoals do
            newGoal.withContext do
              trace[Tactic.librarySearch] "proving {← addMessageContextFull (mkMVar newGoal)}"
              solveByElim newGoal solveByElimDepth
          if (← checkRequired) then
            pure $ some $ Sum.inr ()
          else
            set state0
            pure none
        catch _ =>
          let res := some $ Sum.inl (← getMCtx, newGoals)
          let check ← checkRequired
          set state0
          return if check then res else none)
    catch _ =>
      set state0
      pure none
    match result with
    | none => pure ()
    | some (Sum.inr ()) => return none
    | some (Sum.inl suggestion) => suggestions := suggestions.push suggestion

  pure $ some suggestions
    where
  /-- Verify that the instantiated goal contains each `Expr` in `required` as a sub-expression.
  (Make sure to not reset the state before calling.) -/
  checkRequired : MetaM Bool := return required.all (·.occurs (← instantiateMVars (.mvar goal)))

def lines (ls : List MessageData) :=
  MessageData.joinSep ls (MessageData.ofFormat Format.line)

open Lean.Parser.Tactic

-- TODO: implement the additional options for `library_search` from Lean 3,
-- in particular including additional lemmas
-- with `library_search [X, Y, Z]` or `library_search with attr`.
syntax (name := librarySearch') "library_search" (config)? (simpArgs)?
  (" using " (colGt term),+)? : tactic
syntax (name := librarySearch!) "library_search!" (config)? (simpArgs)?
  (" using " (colGt term),+)? : tactic

-- For now we only implement the basic functionality.
-- The full syntax is recognized, but will produce a "Tactic has not been implemented" error.

open Elab.Tactic Elab Tactic in
elab_rules : tactic | `(tactic| library_search%$tk $[using $[$required:term],*]?) => do
  let mvar ← getMainGoal
  let (_, goal) ← (← getMainGoal).intros
  goal.withContext do
    let required := (← (required.getD #[]).mapM getFVarId).toList.map .fvar
    if let some suggestions ← librarySearch goal (← librarySearchLemmas.get) required then
      for suggestion in suggestions do
        withMCtx suggestion.1 do
          addExactSuggestion tk (← instantiateMVars (mkMVar mvar))
      admitGoal goal
    else
      addExactSuggestion tk (← instantiateMVars (mkMVar mvar))

open Elab Term in
elab tk:"library_search%" : term <= expectedType => do
  let goal ← mkFreshExprMVar expectedType
  let (_, introdGoal) ← goal.mvarId!.intros
  introdGoal.withContext do
    if let some suggestions ← librarySearch introdGoal (← librarySearchLemmas.get) [] then
      for suggestion in suggestions do
        withMCtx suggestion.1 do
          addTermSuggestion tk (← instantiateMVars goal)
      mkSorry expectedType (synthetic := true)
    else
      addTermSuggestion tk (← instantiateMVars goal)
      instantiateMVars goal
