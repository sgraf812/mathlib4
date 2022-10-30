/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/

import Mathlib.Tactic.Linarith.Verification
import Mathlib.Tactic.Linarith.Preprocessing

/-!
# `linarith`: solving linear arithmetic goals

`linarith` is a tactic for solving goals with linear arithmetic.

Suppose we have a set of hypotheses in `n` variables
`S = {a₁x₁ + a₂x₂ + ... + aₙxₙ R b₁x₁ + b₂x₂ + ... + bₙxₙ}`,
where `R ∈ {<, ≤, =, ≥, >}`.
Our goal is to determine if the inequalities in `S` are jointly satisfiable, that is, if there is
an assignment of values to `x₁, ..., xₙ` such that every inequality in `S` is true.

Specifically, we aim to show that they are *not* satisfiable. This amounts to proving a
contradiction. If our goal is also a linear inequality, we negate it and move it to a hypothesis
before trying to prove `false`.

When the inequalities are over a dense linear order, `linarith` is a decision procedure: it will
prove `false` if and only if the inequalities are unsatisfiable. `linarith` will also run on some
types like `ℤ` that are not dense orders, but it will fail to prove `false` on some unsatisfiable
problems. It will run over concrete types like `ℕ`, `ℚ`, and `ℝ`, as well as abstract types that
are instances of `LinearOrderedCommRing`.

## Algorithm sketch

First, the inequalities in the set `S` are rearranged into the form `tᵢ Rᵢ 0`, where
`Rᵢ ∈ {<, ≤, =}` and each `tᵢ` is of the form `∑ cⱼxⱼ`.

`linarith` uses an untrusted oracle to search for a certificate of unsatisfiability.
The oracle searches for a list of natural number coefficients `kᵢ` such that `∑ kᵢtᵢ = 0`, where for
at least one `i`, `kᵢ > 0` and `Rᵢ = <`.

Given a list of such coefficients, `linarith` verifies that `∑ kᵢtᵢ = 0` using a normalization
tactic such as `ring`. It proves that `∑ kᵢtᵢ < 0` by transitivity, since each component of the sum
is either equal to, less than or equal to, or less than zero by hypothesis. This produces a
contradiction.

## Preprocessing

`linarith` does some basic preprocessing before running. Most relevantly, inequalities over natural
numbers are cast into inequalities about integers, and rational division by numerals is canceled
into multiplication. We do this so that we can guarantee the coefficients in the certificate are
natural numbers, which allows the tactic to solve goals over types that are not fields.

Preprocessors are allowed to branch, that is, to case split on disjunctions. `linarith` will succeed
overall if it succeeds in all cases. This leads to exponential blowup in the number of `linarith`
calls, and should be used sparingly. The default preprocessor set does not include case splits.

## Fourier-Motzkin elimination

The oracle implemented to search for certificates uses Fourier-Motzkin variable elimination.
This technique transorms a set of inequalities in `n` variables to an equisatisfiable set in `n - 1`
variables. Once all variables have been eliminated, we conclude that the original set was
unsatisfiable iff the comparison `0 < 0` is in the resulting set.

While performing this elimination, we track the history of each derived comparison. This allows us
to represent any comparison at any step as a positive combination of comparisons from the original
set. In particular, if we derive `0 < 0`, we can find our desired list of coefficients
by counting how many copies of each original comparison appear in the history.

## Implementation details

`linarith` homogenizes numerical constants: the expression `1` is treated as a variable `t₀`.

Often `linarith` is called on goals that have comparison hypotheses over multiple types. This
creates multiple `linarith` problems, each of which is handled separately; the goal is solved as
soon as one problem is found to be contradictory.

Disequality hypotheses `t ≠ 0` do not fit in this pattern. `linarith` will attempt to prove equality
goals by splitting them into two weak inequalities and running twice. But it does not split
disequality hypotheses, since this would lead to a number of runs exponential in the number of
disequalities in the context.

The Fourier-Motzkin oracle is very modular. It can easily be replaced with another function of type
`certificateOracle := List Comp → ℕ → TacticM ((Std.HashMap ℕ ℕ))`,
which takes a list of comparisons and the largest variable
index appearing in those comparisons, and returns a map from comparison indices to coefficients.
An alternate oracle can be specified in the `LinarithConfig` object.

-- TODO Not implemented yet
A variant, `nlinarith`, adds an extra preprocessing step to handle some basic nonlinear goals.
There is a hook in the `linarith_config` configuration object to add custom preprocessing routines.

The certificate checking step is *not* by reflection. `linarith` converts the certificate into a
proof term of type `false`.

Some of the behavior of `linarith` can be inspected with the option
`set_option trace.linarith true`.
Because the variable elimination happens outside the tactic monad, we cannot trace intermediate
steps there.

## File structure

The components of `linarith` are spread between a number of files for the sake of organization.

* `Lemmas.lean` contains proofs of some arithmetic lemmas that are used in preprocessing and in
  verification.
* `Datatypes.lean` contains data structures that are used across multiple files, along with some
  useful auxiliary functions.
* `Preprocessing.lean` contains functions used at the beginning of the tactic to transform
  hypotheses into a shape suitable for the main routine.
* `Parsing.lean` contains functions used to compute the linear structure of an expression.
* `Elimination.lean` contains the Fourier-Motzkin elimination routine.
* `Verification.lean` contains the certificate checking functions that produce a proof of `false`.
* `Frontend.lean` contains the control methods and user-facing components of the tactic.

## Tags

linarith, nlinarith, lra, nra, Fourier-Motzkin, linear arithmetic, linear programming
-/

namespace Linarith

open Lean Elab Tactic Meta
open Std

/-! ### Control -/

/--
If `e` is a comparison `a R b` or the negation of a comparison `¬ a R b`, found in the target,
`get_contr_lemma_name_and_type e` returns the name of a lemma that will change the goal to an
implication, along with the type of `a` and `b`.

For example, if `e` is `(a : ℕ) < b`, returns ``(`lt_of_not_ge, ℕ)``.
-/
def get_contr_lemma_name_and_type (e : Expr) : Option (Name × Expr) :=
match e.getAppFnArgs with
| (``LT.lt, #[t, _, _, _]) => (``lt_of_not_ge, t)
| (``LE.le, #[t, _, _, _]) => (``le_of_not_gt, t)
| (``Eq, #[t, _, _]) => (``eq_of_not_lt_of_not_gt, t)
| (``Ne, #[t, _, _]) => (``Not.intro, t)
| (``GE.ge, #[t, _, _, _]) => (`le_of_not_gt, t)
| (``GT.gt, #[t, _, _, _]) => (`lt_of_not_ge, t)
| (``Not, #[e']) => match e'.getAppFnArgs with
  | (``LT.lt, #[t, _, _, _]) => (``Not.intro, t)
  | (``LE.le, #[t, _, _, _]) => (``Not.intro, t)
  | (``Eq, #[t, _, _]) => (``Not.intro, t)
  | (``GE.ge, #[t, _, _, _]) => (``Not.intro, t)
  | (``GT.gt, #[t, _, _, _]) => (``Not.intro, t)
  | _ => none
| _ => none

/-- Same as `mkConst`, but with fresh level metavariables. -/
def mkConst' (constName : Name) : MetaM Expr := do
  return mkConst constName (← (← getConstInfo constName).levelParams.mapM fun _ => mkFreshLevelMVar)

-- def instantiateTypeMVars (e : Expr) : MetaM Expr := do
--   let t ← instantiateMVars (← inferType e)
--   let m ← mkFreshExprMVar t
--   _ ← isDefEq m e
--   return (← instantiateMVars m)

def getLocalHyps : MetaM (Array Expr) := do
  let mut hs := #[]
  for d in ← getLCtx do
    if !d.isImplementationDetail then hs := hs.push d.toExpr
  return hs

def foo (g : MVarId) : MetaM MVarId := do
  let [g] ← g.apply (mkConst ``Not.intro) | failure
  let (_, g) ← g.intro1P
  return g

def bar (g : MVarId) : MetaM (List MVarId) := do
  let g ← foo g
  g.withContext do
    let hyps ← getLocalHyps
    logInfo m!"{hyps}"
    let types ← hyps.mapM inferType
    let types ← types.mapM instantiateMVars
    logInfo m!"{types}"
    return [g]

elab "bar" : tactic => do liftMetaTactic bar

example (h : 0 < 1) : ¬ 7 < 3 := by
  bar
  admit

/--
`apply_contr_lemma` inspects the target to see if it can be moved to a hypothesis by negation.
For example, a goal `⊢ a ≤ b` can become `a > b ⊢ false`.
If this is the case, it applies the appropriate lemma and introduces the new hypothesis.
It returns the type of the terms in the comparison (e.g. the type of `a` and `b` above) and the
newly introduced local constant.
Otherwise returns `none`.
-/
def apply_contr_lemma (g : MVarId) : MetaM (Option (Expr × Expr) × MVarId) := do
  match get_contr_lemma_name_and_type (← g.getType) with
  | some (nm, tp) => do
      let [g] ← g.apply (← mkConst' nm) | failure
      let (f, g) ← g.intro1P
      return (some (tp, .fvar f), g)
  | none => return (none, g)



/--
`partition_by_type l` takes a list `l` of proofs of comparisons. It sorts these proofs by
the type of the variables in the comparison, e.g. `(a : ℚ) < 1` and `(b : ℤ) > c` will be separated.
Returns a map from a type to a list of comparisons over that type.
-/
def partition_by_type (l : List Expr) : MetaM (Std.HashMap Expr (List Expr)) :=
l.foldlM (fun m h => do return m.consVal (← ineq_prf_tp h) h) HashMap.empty

/--
Given a list `ls` of lists of proofs of comparisons, `try_linarith_on_lists cfg ls` will try to
prove `false` by calling `linarith` on each list in succession. It will stop at the first proof of
`false`, and fail if no contradiction is found with any list.
-/
def try_linarith_on_lists (cfg : LinarithConfig) (g : MVarId) (ls : List (List Expr)) : TermElabM Expr :=
ls.firstM (fun L => proveFalseByLinarith cfg g L)
  <|> throwError "linarith failed to find a contradiction"

-- There is a `TacticM` level version of this, but I want it in `MetaM` ...
def ensureHasNoMVars (e : Expr) : MetaM Unit := do
  let e ← instantiateMVars e
  if e.hasExprMVar then
    throwError "tactic failed, resulting expression contains metavariables{indentExpr e}"

/--
Given a list `hyps` of proofs of comparisons, `run_linarith_on_pfs cfg hyps pref_type`
preprocesses `hyps` according to the list of preprocessors in `cfg`.
This results in a list of branches (typically only one),
each of which must succeed in order to close the goal.

In each branch, we partition the  list of hypotheses by type, and run `linarith` on each class
in the partition; one of these must succeed in order for `linarith` to succeed on this branch.
If `pref_type` is given, it will first use the class of proofs of comparisons over that type.
-/
-- If it succeeds, the passed metavariable should have been assigned.
def run_linarith_on_pfs (cfg : LinarithConfig) (pref_type : Option Expr) (g : MVarId)
    (hyps : List Expr) : TermElabM Unit :=
-- TODO make more idiomatic
let single_process : MVarId → List Expr → TermElabM Expr :=
  fun (g : MVarId) (hyps : List Expr) => do
   linarithTraceProofs
     ("after preprocessing, linarith has " ++ toString hyps.length ++ " facts:") hyps
   let hyp_set ← partition_by_type hyps
   linarithTrace m!"hypotheses appear in {hyp_set.size} different types"
   match pref_type with
   | some t => proveFalseByLinarith cfg g (hyp_set.findD t []) <|>
               try_linarith_on_lists cfg g ((hyp_set.erase t).values)
   | none => try_linarith_on_lists cfg g hyp_set.values
let preprocessors := cfg.preprocessors.getD default_preprocessors
-- TODO restore when the `remove_ne` preprocessor is implemented
-- let preprocessors := if cfg.split_ne then linarith.remove_ne::preprocessors else preprocessors
do
  let branches ← preprocess preprocessors g hyps
  for (g, es) in branches do
    let r ← single_process g es
    g.assign r
  -- Verify that we closed the goal. Failure here should only result from a bad `Preprocessor`.
  ensureHasNoMVars (.mvar g)

/--
`filter_hyps_to_type restr_type hyps` takes a list of proofs of comparisons `hyps`, and filters it
to only those that are comparisons over the type `restr_type`.
-/
def filter_hyps_to_type (restr_type : Expr) (hyps : List Expr) : MetaM (List Expr) :=
hyps.filterM (fun h => do
  let ht ← inferType h
  match get_contr_lemma_name_and_type ht with
  | some (_, htype) => isDefEq htype restr_type
  | none => return false)

-- TODO not sure what this is for, omit for now.
-- /-- A hack to allow users to write `{restr_type := ℚ}` in configuration structures. -/
-- meta def get_restrict_type (e : expr) : tactic expr :=
-- do m ← mk_mvar,
--    unify `(some %%m : option Type) e,
--    instantiate_mvars m

end Linarith

/-! ### User facing functions -/

open Linarith
open Lean Elab Tactic Meta


/--
Run a tactic on all goals, and always succeeds.

(This is parallel to `Lean.Elab.Tactic.evalAllGoals` in core,
which takes a `Syntax` rather than `TacticM Unit`.
This function could be moved to core and `evalAllGoals` refactored to use it.)
-/
def allGoals (tac : TacticM Unit) : TacticM Unit := do
  let mvarIds ← getGoals
  let mut mvarIdsNew := #[]
  for mvarId in mvarIds do
    unless (← mvarId.isAssigned) do
      setGoals [mvarId]
      try
        tac
        mvarIdsNew := mvarIdsNew ++ (← getUnsolvedGoals)
      catch ex =>
        if (← read).recover then
          logException ex
          mvarIdsNew := mvarIdsNew.push mvarId
        else
          throw ex
  setGoals mvarIdsNew.toList


-- def F (f : α → β → MetaM (γ × α)) (a : α) (bs : Array β) : MetaM (Array γ × α) := do
--   let mut z := a
--   let mut gs : Array γ := #[]
--   for b in bs do
--     let (g, a') ← f z b
--     z := a'
--     gs := gs.push g
--   return (gs, z)

-- #eval F (fun n m => return (n*m, n+1)) 0 #[1,2,3,4]

-- def G (f : α → β → MetaM (γ × α)) : β → StateT α MetaM γ := fun b => do
--   let (g, a) ← f (←get) b
--   set a
--   return g

-- def F' (f : α → β → MetaM (γ × α)) (a : α) (bs : Array β) : MetaM (Array γ × α) := do
--   StateT.run (bs.mapM (G f)) a

-- #eval F' (fun n m => return (n+1, n*m)) 0 #[1,2,3,4] -- (#[0, 2, 6, 12], 4)

-- /-- Asserts an expression as an anonymous hypothesis. -/
-- def noteAnonymous (g : MVarId) (e : Expr) : MetaM (FVarId × MVarId) := do
--   (← g.assert .anonymous (←inferType e) e).intro1P

-- /-- Asserts an array of expressions as anonymous hypotheses. -/
-- def noteAllAnonymous (g : MVarId) (es : Array Expr) : MetaM (Array FVarId × MVarId) := do
--   let mut z := g
--   let mut fs : Array FVarId := Array.mkEmpty es.size
--   for e in es do
--     let (f, g') ← noteAnonymous z e
--     z := g'
--     fs := fs.push f
--   return (fs, z)

/--
`linarith reduce_semi only_on hyps cfg` tries to close the goal using linear arithmetic. It fails
if it does not succeed at doing this.

* If `reduce_semi` is true, it will unfold semireducible definitions when trying to match atomic
expressions.
* `hyps` is a list of proofs of comparisons to include in the search.
* If `only_on` is true, the search will be restricted to `hyps`. Otherwise it will use all
  comparisons in the local context.
-/
partial def tactic.linarith (reduce_semi : Bool) (only_on : Bool) (hyps : List Expr)
  (cfg : LinarithConfig := {}) (g : MVarId) : MetaM (List MVarId) := -- TODO add like `liftMetaFinishingTactic`? and change to `MetaM Unit`
-- TODO make this better Lean4 style: lower the monads where possible, handle goals cleanly!
do
  linarithTrace "waking up"
  logInfo m!"{g}"
  -- if the target is an equality, we run `linarith` twice, to prove ≤ and ≥.
  if (← g.getType).isEq then do
    linarithTrace "target is an equality: splitting"
    let [g₁, g₂] ← g.apply (← mkConst' ``eq_of_not_lt_of_not_gt) | failure
    -- TODO This is a bit silly, as we know that both lists are empty.
    return (← tactic.linarith reduce_semi only_on hyps cfg g₁) ++
      (← tactic.linarith reduce_semi only_on hyps cfg g₂)
  else do
    -- TODO this step is unnecessary, right? There's no need to note expressions as hypotheses.
    -- let (hyps, g) ← noteAllAnonymous (←getMainGoal) hyps
    if cfg.split_hypotheses then do
      linarithTrace "trying to split hypotheses"
      -- TODO `auto.split_hyps` hasn't been ported.
      -- try auto.split_hyps
  /- If we are proving a comparison goal (and not just `false`), we consider the type of the
    elements in the comparison to be the "preferred" type. That is, if we find comparison
    hypotheses in multiple types, we will run `linarith` on the goal type first.
    In this case we also receive a new variable from moving the goal to a hypothesis.
    Otherwise, there is no preferred type and no new variable; we simply change the goal to `false`.
  -/

    -- TODO can we rename liftMetaTacticAux?
    -- TODO do this with a match
    let (pref_type_and_new_var_from_tgt, g) ← apply_contr_lemma g
    logInfo m!"{g}"
    -- FIXME we never escape this block??
    -- let [g] ← if pref_type_and_new_var_from_tgt.isNone then
    --   if cfg.exfalso then
    --     linarithTrace "using exfalso"
    --     g.apply (← mkConst' ``False.elim) -- TODO A `MetaM` level `exfalso`, please?
    --   else throwError "linarith failed: target is not a valid comparison"
    -- else return [g] | throwError "huh"

    -- TODO we should do this outside
    -- let cfg := cfg.updateReducibility reduce_semi
    let (pref_type, new_var) :=
      pref_type_and_new_var_from_tgt.elim (none, none) (Prod.map some some)

    -- withMainContext do
    linarithTrace "after apply_contr_lemma"
    g.withContext do
    -- set up the list of hypotheses, considering the `only_on` and `restrict_type` options
      let hyps ← (if only_on then do return new_var.toList ++ hyps
        else do return (← getLocalHyps).toList ++ hyps)
      logInfo m!"{hyps}"
    -- TODO restore handling of restricting types:
    -- let hyps ← (do
    --   let t ← get_restrict_type cfg.restrict_type_reflect
    --   filter_hyps_to_type t hyps) <|>
    --   return hyps

      linarithTraceProofs "linarith is running on the following hypotheses:" hyps
      run_linarith_on_pfs cfg pref_type g hyps |>.run'
    -- failure
    return []

open Parser Tactic
open Syntax

syntax (name := linarith) "linarith" (config)? (&" only")? (" [" term,* "]")? : tactic
syntax (name := linarith!) "linarith!" (config)? (&" only")? (" [" term,* "]")? : tactic

declare_config_elab elabLinarithConfig LinarithConfig

/--
Tries to prove a goal of `false` by linear arithmetic on hypotheses.
If the goal is a linear (in)equality, tries to prove it by contradiction.
If the goal is not `false` or an inequality, applies `exfalso` and tries linarith on the
hypotheses.

* `linarith` will use all relevant hypotheses in the local context.
* `linarith [t1, t2, t3]` will add proof terms t1, t2, t3 to the local context.
* `linarith only [h1, h2, h3, t1, t2, t3]` will use only the goal (if relevant), local hypotheses
  `h1`, `h2`, `h3`, and proofs `t1`, `t2`, `t3`. It will ignore the rest of the local context.
* `linarith!` will use a stronger reducibility setting to identify atoms.

Config options:
* `linarith {exfalso := ff}` will fail on a goal that is neither an inequality nor `false`
* `linarith {restrict_type := T}` will run only on hypotheses that are inequalities over `T`
* `linarith {discharger := tac}` will use `tac` instead of `ring` for normalization.
  Options: `ring2`, `ring SOP`, `simp`
* `linarith {split_hypotheses := ff}` will not destruct conjunctions in the context.
-/
elab_rules : tactic
  | `(tactic| linarith $[$cfg]? $[only%$o]? $[[$args,*]]?) => do
    liftMetaTactic <|
      tactic.linarith false o.isSome
        (← ((args.map (TSepArray.getElems)).getD {}).mapM (elabTerm ·.raw none)).toList
        (← elabLinarithConfig (mkOptionalNode cfg))

set_option trace.linarith true

open Function

set_option pp.all true
example [LinearOrderedCommRing α] [Nontrivial α] {a b : α} (h : a < b) (w : b < a) : False := by
  linarith

#exit

example (h : 1 < 0) (g : ¬ 37 < 42) (k : True) /-(l : (-7 : ℤ) < 5)-/: 3 < 7 := by
  linarith [(rfl : 0 = 0)]
  all_goals admit


example (h : 1 < 0) : 3 = 7 := by
  linarith [Int.zero_lt_one]
  all_goals admit

-- TODO We have to repeat all that just to handle the `!`?
-- Copy doc-string?
elab_rules : tactic
  | `(tactic| linarith! $[$cfg]? $[only%$o]? $[[$args,*]]?) => do
    liftMetaTactic <|
      tactic.linarith true o.isSome
        (← ((args.map (TSepArray.getElems)).getD {}).mapM (elabTerm ·.raw none)).toList
        (← elabLinarithConfig (mkOptionalNode cfg))

-- add_hint_tactic "linarith"

/-
`linarith` attempts to find a contradiction between hypotheses that are linear (in)equalities.
Equivalently, it can prove a linear inequality by assuming its negation and proving `false`.

In theory, `linarith` should prove any goal that is true in the theory of linear arithmetic over
the rationals. While there is some special handling for non-dense orders like `nat` and `int`,
this tactic is not complete for these theories and will not prove every true goal. It will solve
goals over arbitrary types that instantiate `linear_ordered_comm_ring`.

An example:
```lean
example (x y z : ℚ) (h1 : 2*x  < 3*y) (h2 : -4*x + 2*z < 0)
        (h3 : 12*y - 4* z < 0)  : false :=
by linarith
```

`linarith` will use all appropriate hypotheses and the negation of the goal, if applicable.

`linarith [t1, t2, t3]` will additionally use proof terms `t1, t2, t3`.

`linarith only [h1, h2, h3, t1, t2, t3]` will use only the goal (if relevant), local hypotheses
`h1`, `h2`, `h3`, and proofs `t1`, `t2`, `t3`. It will ignore the rest of the local context.

`linarith!` will use a stronger reducibility setting to try to identify atoms. For example,
```lean
example (x : ℚ) : id x ≥ x :=
by linarith
```
will fail, because `linarith` will not identify `x` and `id x`. `linarith!` will.
This can sometimes be expensive.

`linarith {discharger := tac, restrict_type := tp, exfalso := ff}` takes a config object with five
optional arguments:
* `discharger` specifies a tactic to be used for reducing an algebraic equation in the
  proof stage. The default is `ring`. Other options currently include `ring SOP` or `simp` for basic
  problems.
* `restrict_type` will only use hypotheses that are inequalities over `tp`. This is useful
  if you have e.g. both integer and rational valued inequalities in the local context, which can
  sometimes confuse the tactic.
* `transparency` controls how hard `linarith` will try to match atoms to each other. By default
  it will only unfold `reducible` definitions.
* If `split_hypotheses` is true, `linarith` will split conjunctions in the context into separate
  hypotheses.
* If `exfalso` is false, `linarith` will fail when the goal is neither an inequality nor `false`.
  (True by default.)

A variant, `nlinarith`, does some basic preprocessing to handle some nonlinear goals.

The option `set_option trace.linarith true` will trace certain intermediate stages of the `linarith`
routine.
-/
-- add_tactic_doc
-- { name       := "linarith",
--   category   := doc_category.tactic,
--   decl_names := [`tactic.interactive.linarith],
--   tags       := ["arithmetic", "decision procedure", "finishing"] }

/-
An extension of `linarith` with some preprocessing to allow it to solve some nonlinear arithmetic
problems. (Based on Coq's `nra` tactic.) See `linarith` for the available syntax of options,
which are inherited by `nlinarith`; that is, `nlinarith!` and `nlinarith only [h1, h2]` all work as
in `linarith`. The preprocessing is as follows:

* For every subterm `a ^ 2` or `a * a` in a hypothesis or the goal,
  the assumption `0 ≤ a ^ 2` or `0 ≤ a * a` is added to the context.
* For every pair of hypotheses `a1 R1 b1`, `a2 R2 b2` in the context, `R1, R2 ∈ {<, ≤, =}`,
  the assumption `0 R' (b1 - a1) * (b2 - a2)` is added to the context (non-recursively),
  where `R ∈ {<, ≤, =}` is the appropriate comparison derived from `R1, R2`.
-/
-- meta def tactic.interactive.nlinarith (red : parse ((tk "!")?))
--   (restr : parse ((tk "only")?)) (hyps : parse pexpr_list?)
--   (cfg : linarith_config := {}) : tactic unit :=
-- tactic.linarith red.is_some restr.is_some (hyps.get_or_else [])
--   { cfg with preprocessors := some $
--       cfg.preprocessors.get_or_else default_preprocessors ++ [nlinarith_extras] }

-- add_hint_tactic "nlinarith"

-- add_tactic_doc
-- { name       := "nlinarith",
--   category   := doc_category.tactic,
--   decl_names := [`tactic.interactive.nlinarith],
--   tags       := ["arithmetic", "decision procedure", "finishing"] }
