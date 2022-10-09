/-
Copyright (c) 2020 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
import Lean
import Mathlib.Lean.Expr.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Util.SynthesizeUsing
import Mathlib.Mathport.Syntax
import Qq

/-!
# Datatypes for `linarith`

Some of the data structures here are used in multiple parts of the tactic.
We split them into their own file.

This file also contains a few convenient auxiliary functions.
-/

-- TODO finish snake casing

open Lean Elab Tactic

initialize registerTraceClass `Tactic.linarith

namespace Linarith

/-- A shorthand for tracing when the `trace.Tactic.linarith` option is set to true. -/
def linarith_trace {α} [ToMessageData α] (s : α) : CoreM Unit := do
  trace[linarith] "{s}"

/--
A shorthand for tracing the types of a list of proof terms
when the `trace.Tactic.linarith` option is set to true.
-/
def linarith_trace_proofs (s : String := "") (l : List Expr) : MetaM Unit := do
  trace[linarith] s
  trace[linarith] (← l.mapM Meta.inferType)

/-! ### Linear expressions -/

/--
A linear expression is a list of pairs of variable indices and coefficients,
representing the sum of the products of each coefficient with its corresponding variable.

Some functions on `Linexp` assume that `n : Nat` occurs at most once as the first element of a pair,
and that the list is sorted in decreasing order of the first argument.
This is not enforced by the type but the operations here preserve it.
-/
@[reducible]
def Linexp : Type := List (Nat × Int)

namespace Linexp
/--
Add two `Linexp`s together componentwise.
Preserves sorting and uniqueness of the first argument.
-/
partial def add : Linexp → Linexp → Linexp
| [], a => a
| a, [] => a
| (a@(n1,z1)::t1), (b@(n2,z2)::t2) =>
  if n1 < n2 then b::add (a::t1) t2
  else if n2 < n1 then a::add t1 (b::t2)
  else
    let sum := z1 + z2
    if sum = 0 then add t1 t2 else (n1, sum)::add t1 t2

/-- `l.scale c` scales the values in `l` by `c` without modifying the order or keys. -/
def scale (c : Int) (l : Linexp) : Linexp :=
  if c = 0 then []
  else if c = 1 then l
  else l.map $ fun ⟨n, z⟩ => (n, z*c)

/--
`l.get n` returns the value in `l` associated with key `n`, if it exists, and `none` otherwise.
This function assumes that `l` is sorted in decreasing order of the first argument,
that is, it will return `none` as soon as it finds a key smaller than `n`.
-/
def get (n : Nat) : Linexp → Option Int
| [] => none
| ((a, b)::t) =>
  if a < n then none
  else if a = n then some b
  else get n t

/--
`l.contains n` is true iff `n` is the first element of a pair in `l`.
-/
def contains (n : Nat) : Linexp → Bool := Option.isSome ∘ get n

/--
`l.zfind n` returns the value associated with key `n` if there is one, and 0 otherwise.
-/
def zfind (n : Nat) (l : Linexp) : Int :=
match l.get n with
| none => 0
| some v => v

/-- `l.vars` returns the list of variables that occur in `l`. -/
def vars (l : Linexp) : List Nat :=
  l.map Prod.fst

/--
Defines a lex ordering on `Linexp`. This function is performance critical.
-/
def cmp : Linexp → Linexp → Ordering
| [], [] => Ordering.eq
| [], _ => Ordering.lt
| _, [] => Ordering.gt
| ((n1,z1)::t1), ((n2,z2)::t2) =>
  if n1 < n2 then Ordering.lt
  else if n2 < n1 then Ordering.gt
  else if z1 < z2 then Ordering.lt
  else if z2 < z1 then Ordering.gt
  else cmp t1 t2

end Linexp

/-! ### Inequalities -/

/-- The three-element type `Ineq` is used to represent the strength of a comparison between
terms. -/
inductive Ineq : Type
| eq | le | lt
deriving DecidableEq, Inhabited

namespace Ineq

/--
`max R1 R2` computes the strength of the sum of two inequalities. If `t1 R1 0` and `t2 R2 0`,
then `t1 + t2 (max R1 R2) 0`.
-/
def max : Ineq → Ineq → Ineq
| lt, _ => lt
| _, lt => lt
| le, _ => le
| _, le => le
| eq, eq => eq

/-- `Ineq` is ordered `eq < le < lt`. -/
def cmp : Ineq → Ineq → Ordering
| eq, eq => Ordering.eq
| eq, _ => Ordering.lt
| le, le => Ordering.eq
| le, lt => Ordering.lt
| lt, lt => Ordering.eq
| _, _ => Ordering.gt

/-- Prints an `Ineq` as the corresponding infix symbol. -/
def toString : Ineq → String
| eq => "="
| le => "≤"
| lt => "<"

/-- Finds the name of a multiplicative lemma corresponding to an inequality strength. -/
-- FIXME
def to_const_mul_nm : Ineq → Name
| _ => sorry
-- | lt => ``mul_neg
-- | le => ``mul_nonpos
-- | eq => ``mul_eq


instance : ToString Ineq := ⟨toString⟩

instance : ToFormat Ineq := ⟨fun i => Ineq.toString i⟩

end Ineq

/-! ### Comparisons with 0 -/

/--
The main datatype for FM elimination.
Variables are represented by natural numbers, each of which has an integer coefficient.
Index 0 is reserved for constants, i.e. `coeffs.find 0` is the coefficient of 1.
The represented term is `coeffs.sum (λ ⟨k, v⟩, v * Var[k])`.
str determines the strength of the comparison -- is it < 0, ≤ 0, or = 0?
-/
structure Comp : Type :=
  (str : Ineq)
  (coeffs : Linexp)
deriving Inhabited

/-- `c.vars` returns the list of variables that appear in the linear expression contained in `c`. -/
def Comp.vars : Comp → List Nat := Linexp.vars ∘ Comp.coeffs

/-- `c.coeff_of a` projects the coefficient of variable `a` out of `c`. -/
def Comp.coeff_of (c : Comp) (a : Nat) : Int :=
  c.coeffs.zfind a

/-- `c.scale n` scales the coefficients of `c` by `n`. -/
def Comp.scale (c : Comp) (n : Nat) : Comp :=
  { c with coeffs := c.coeffs.scale n }

/--
`Comp.add c1 c2` adds the expressions represented by `c1` and `c2`.
The coefficient of variable `a` in `c1.add c2`
is the sum of the coefficients of `a` in `c1` and `c2`.
 -/
def Comp.add (c1 c2 : Comp) : Comp :=
  ⟨c1.str.max c2.str, c1.coeffs.add c2.coeffs⟩

/-- `Comp` has a lex order. First the `ineq`s are compared, then the `coeff`s. -/
def Comp.cmp : Comp → Comp → Ordering
| ⟨str1, coeffs1⟩, ⟨str2, coeffs2⟩ =>
  match str1.cmp str2 with
  | Ordering.lt => Ordering.lt
  | Ordering.gt => Ordering.gt
  | Ordering.eq => coeffs1.cmp coeffs2

/--
A `Comp` represents a contradiction if its expression has no coefficients and its strength is <,
that is, it represents the fact `0 < 0`.
 -/
def Comp.isContr (c : Comp) : Bool := c.coeffs.isEmpty && c.str = Ineq.lt

instance Comp.ToFormat : ToFormat Comp :=
  ⟨fun p => format p.coeffs ++ toString p.str ++ "0"⟩

/-! ### Parsing into linear form -/


/-! ### Control -/

/--
A preprocessor transforms a proof of a proposition into a proof of a different propositon.
The return type is `List Expr`, since some preprocessing steps may create multiple new hypotheses,
and some may remove a hypothesis from the list.
A "no-op" preprocessor should return its input as a singleton list.
-/
structure Preprocessor : Type :=
  (name : String)
  (transform : Expr → TacticM (List Expr)) -- FIXME which monad is appropriate here?

/--
Some preprocessors need to examine the full list of hypotheses instead of working item by item.
As with `Preprocessor`, the input to a `GlobalPreprocessor` is replaced by, not added to, its
output.
-/
structure GlobalPreprocessor : Type :=
  (name : String)
  (transform : List Expr → TacticM (List Expr)) -- FIXME which monad is appropriate here?

/--
Some preprocessors perform branching case splits. A `Branch` is used to track one of these case
splits. The first component, an `MVarId`, is the goal corresponding to this branch of the split,
given as a metavariable. The `List Expr` component is the list of hypotheses for `linarith`
in this branch. Every `Expr` in this list should be type correct in the context of the associated
goal.
-/
def Branch : Type := MVarId × List Expr

/--
Some preprocessors perform branching case splits.
A `GlobalBranchingPreprocessor` produces a list of branches to run.
Each branch is independent, so hypotheses that appear in multiple branches should be duplicated.
The preprocessor is responsible for making sure that each branch contains the correct goal
metavariable.
-/
structure GlobalBranchingPreprocessor : Type :=
  (name : String)
  (transform : List Expr → TacticM (List Branch)) -- FIXME which monad is appropriate here?

/--
A `Preprocessor` lifts to a `GlobalPreprocessor` by folding it over the input list.
-/
def Preprocessor.globalize (pp : Preprocessor) : GlobalPreprocessor :=
{ name := pp.name,
  transform := List.foldlM (fun ret e => do return (← pp.transform e) ++ ret) [] }

/--
A `GlobalPreprocessor` lifts to a `GlobalBranchingPreprocessor` by producing only one branch.
-/
def GlobalPreprocessor.branching (pp : GlobalPreprocessor) : GlobalBranchingPreprocessor :=
{ name := pp.name,
  transform := fun l => do return [⟨← getMainGoal, ← pp.transform l⟩] }

/--
`process pp l` runs `pp.transform` on `l` and returns the result,
tracing the result if `trace.linarith` is on.
-/
def GlobalBranchingPreprocessor.process (pp : GlobalBranchingPreprocessor)
  (l : List Expr) : TacticM (List Branch) := do
  let branches ← pp.transform l
  if (branches.length > 1) then
    linarith_trace (format "Preprocessing: {pp.name} has branched, with branches:")
  for ⟨goal, hyps⟩ in branches do
    setGoals [goal]
    linarith_trace_proofs (toString (format "Preprocessing: {pp.name}")) hyps
  return branches

instance PreprocessorToGlobalBranchingPreprocessor :
    Coe Preprocessor GlobalBranchingPreprocessor :=
  ⟨GlobalPreprocessor.branching ∘ Preprocessor.globalize⟩

instance GlobalPreprocessorToGlobalBranchingPreprocessor :
    Coe GlobalPreprocessor GlobalBranchingPreprocessor :=
  ⟨GlobalPreprocessor.branching⟩


/--
A `CertificateOracle` is a function
`produce_certificate : List Comp → Nat → TacticM (HashMap Nat Nat)`.
`produce_certificate hyps max_var` tries to derive a contradiction from the comparisons in `hyps`
by eliminating all variables ≤ `max_var`.
If successful, it returns a map `coeff : Nat → Nat` as a certificate.
This map represents that we can find a contradiction by taking the sum  `∑ (coeff i) * hyps[i]`.

The default `CertificateOracle` used by `linarith` is
`linarith.fourier_motzkin.produce_certificate`.
-/
def CertificateOracle : Type :=
  List Comp → Nat → TacticM (Std.HashMap Nat Nat)

open Meta

/-- A configuration object for `linarith`. -/
structure LinarithConfig : Type 2 :=
  (discharger : TacticM Unit := do evalTactic (←`(tactic| ring))) -- TODO There should be a def for this?
  (restrict_type : Option Type := none)
  -- FIXME err... do we need this?
  -- (restrict_type_reflect : reflected _ restrict_type . tactic.apply_instance)
  (exfalso : Bool := true)
  (transparency : TransparencyMode := .reducible)
  (split_hypotheses : Bool := true)
  (split_ne : Bool := false)
  (preprocessors : Option (List GlobalBranchingPreprocessor) := none)
  (oracle : Option CertificateOracle := none)

/--
`cfg.update_reducibility reduce_default` will change the transparency setting of `cfg` to
`default` if `reduce_default` is true. In this case, it also sets the discharger to `ring!`,
since this is typically needed when using stronger unification.
-/
def LinarithConfig.update_reducibility (cfg : LinarithConfig) (reduce_default : Bool) :
    LinarithConfig :=
  if reduce_default then
    { cfg with transparency := .default, discharger := do evalTactic (←`(tactic| ring!)) }
  else cfg

/-!
### Auxiliary functions

These functions are used by multiple modules, so we put them here for accessibility.
-/

open tactic

/--
`get_rel_sides e` returns the left and right hand sides of `e` if `e` is a comparison,
and fails otherwise.
This function is more naturally in the `Option` monad, but it is convenient to put in `TacticM`
for compositionality.
 -/
def get_rel_sides (e : Expr) : TacticM (Expr × Expr) :=
  match e.getAppFnArgs with
  | (``LT.lt, #[a, b]) => return (a, b)
  | (``LE.le, #[a, b]) => return (a, b)
  | (``Eq, #[a, b]) => return (a, b)
  | (``GE.ge, #[a, b]) => return (a, b)
  | (``GT.gt, #[a, b]) => return (a, b)
  | _ => throwError "Not a comparison"

open Qq

/--
`parse_into_comp_and_expr e` checks if `e` is of the form `t < 0`, `t ≤ 0`, or `t = 0`.
If it is, it returns the comparison along with `t`.
-/
def parse_into_comp_and_expr : Q(Prop) → MetaM (Option (Ineq × Expr))
| ~q($e < 0) => return some (Ineq.lt, e)
| ~q($e ≤ 0) => return some (Ineq.le, e)
| ~q($e = 0) => return some (Ineq.eq, e)
| _ => return none

/--
`mk_single_comp_zero_pf c h` assumes that `h` is a proof of `t R 0`.
It produces a pair `(R', h')`, where `h'` is a proof of `c*t R' 0`.
Typically `R` and `R'` will be the same, except when `c = 0`, in which case `R'` is `=`.
If `c = 1`, `h'` is the same as `h` -- specifically, it does *not* change the type to `1*t R 0`.
-/
def mk_single_comp_zero_pf (c : Nat) (h : Expr) : TacticM (Ineq × Expr) := do
  let tp ← inferType h
  let some (iq, e) ← parse_into_comp_and_expr tp | throwError "invalid comparison: {h} : {tp}"
  if c = 0 then do
    let e' ← mkAppM ``zero_mul #[e]
    return (Ineq.eq, e')
  else if c = 1 then return (iq, h)
  else do
    let tp ← inferType (← get_rel_sides (← inferType h)).2
    let cpos ← mkAppM ``GT.gt #[(← tp.ofNat c), (← tp.ofNat 0)]
    let ex ← synthesizeUsing cpos (do evalTactic (←`(tactic| norm_num; done)))
    let e' ← mkAppM iq.to_const_mul_nm #[h, ex]
    return (iq, e')