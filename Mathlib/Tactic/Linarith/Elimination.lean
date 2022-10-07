/-
Copyright (c) 2020 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/

import Mathlib.Data.HashSet
import Mathlib.Data.RBSet
import Mathlib.Tactic.Linarith.Datatypes

-- TODO finish snake-casing

/-!
# The Fourier-Motzkin elimination procedure

The Fourier-Motzkin procedure is a variable elimination method for linear inequalities.
<https://en.wikipedia.org/wiki/Fourier%E2%80%93Motzkin_elimination>

Given a set of linear inequalities `comps = {tᵢ Rᵢ 0}`,
we aim to eliminate a single variable `a` from the set.
We partition `comps` into `comps_pos`, `comps_neg`, and `comps_zero`,
where `comps_pos` contains the comparisons `tᵢ Rᵢ 0` in which
the coefficient of `a` in `tᵢ` is positive, and similar.

For each pair of comparisons `tᵢ Rᵢ 0 ∈ comps_pos`, `tⱼ Rⱼ 0 ∈ comps_neg`,
we compute coefficients `vᵢ, vⱼ ∈ ℕ` such that `vᵢ*tᵢ + vⱼ*tⱼ` cancels out `a`.
We collect these sums `vᵢ*tᵢ + vⱼ*tⱼ R' 0` in a set `S` and set `comps' = S ∪ comps_zero`,
a new set of comparisons in which `a` has been eliminated.

Theorem: `comps` and `comps'` are equisatisfiable.

We recursively eliminate all variables from the system. If we derive an empty clause `0 < 0`,
we conclude that the original system was unsatisfiable.
-/

open Std

namespace Linarith

/-!
### Datatypes

The `comp_source` and `pcomp` datatypes are specific to the FM elimination routine;
they are not shared with other components of `linarith`.
-/

/--
`comp_source` tracks the source of a comparison.
The atomic source of a comparison is an assumption, indexed by a natural number.
Two comparisons can be added to produce a new comparison,
and one comparison can be scaled by a natural number to produce a new comparison.
 -/
-- FIXME @[derive inhabited]
inductive CompSource : Type
| assump : Nat → CompSource
| add : CompSource → CompSource → CompSource
| scale : Nat → CompSource → CompSource

/--
Given a `CompSource` `cs`, `cs.flatten` maps an assumption index
to the number of copies of that assumption that appear in the history of `cs`.

For example, suppose `cs` is produced by scaling assumption 2 by 5,
and adding to that the sum of assumptions 1 and 2.
`cs.flatten` maps `1 ↦ 1, 2 ↦ 6`.
 -/
def CompSource.flatten : CompSource → HashMap Nat Nat
| (CompSource.assump n) => HashMap.empty.insert n 1
| (CompSource.add c1 c2) => (CompSource.flatten c1).add (CompSource.flatten c2)
| (CompSource.scale n c) => (CompSource.flatten c).mapVal (fun _ v => v * n)

/-- Formats a `comp_source` for printing. -/
def CompSource.toString : CompSource → String
| (CompSource.assump e) => ToString.toString e
| (CompSource.add c1 c2) => CompSource.toString c1 ++ " + " ++ CompSource.toString c2
| (CompSource.scale n c) => ToString.toString n ++ " * " ++ CompSource.toString c

instance CompSource.ToFormat : ToFormat CompSource :=
  ⟨fun a => CompSource.toString a⟩

/--
A `PComp` stores a linear comparison `Σ cᵢ*xᵢ R 0`,
along with information about how this comparison was derived.
The original expressions fed into `linarith` are each assigned a unique natural number label.
The *historical set* `PComp.history` stores the labels of expressions
that were used in deriving the current `PComp`.
Variables are also indexed by natural numbers. The sets `PComp.effective`, `PComp.implicit`,
and `PComp.vars` contain variable indices.
* `PComp.vars` contains the variables that appear in `PComp.c`. We store them in `PComp` to
  avoid recomputing the set, which requires folding over a list. (TODO: is this really needed?)
* `PComp.effective` contains the variables that have been effectively eliminated from `PComp`.
  A variable `n` is said to be *effectively eliminated* in `PComp` if the elimination of `n`
  produced at least one of the ancestors of `PComp`.
* `PComp.implicit` contains the variables that have been implicitly eliminated from `PComp`.
  A variable `n` is said to be *implicitly eliminated* in `PComp` if it satisfies the following
  properties:
  - There is some `ancestor` of `PComp` such that `n` appears in `ancestor.vars`.
  - `n` does not appear in `PComp.vars`.
  - `n` was not effectively eliminated.

We track these sets in order to compute whether the history of a `PComp` is *minimal*.
Checking this directly is expensive, but effective approximations can be defined in terms of these
sets. During the variable elimination process, a `PComp` with non-minimal history can be discarded.
-/
structure PComp : Type :=
  (c : Comp)
  (src : CompSource)
  (history : HashSet ℕ)
  (effective : HashSet ℕ)
  (implicit : HashSet ℕ)
  (vars : HashSet ℕ)

/--
Any comparison whose history is not minimal is redundant,
and need not be included in the new set of comparisons.
`elimed_ge : ℕ` is a natural number such that all variables with index ≥ `elimed_ge` have been
removed from the system.

This test is an overapproximation to minimality. It gives necessary but not sufficient conditions.
If the history of `c` is minimal, then `c.maybe_minimal` is true,
but `c.maybe_minimal` may also be true for some `c` with minimal history.
Thus, if `c.maybe_minimal` is false, `c` is known not to be minimal and must be redundant.
See http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.51.493&rep=rep1&type=pdf p.13
(Theorem 7).
The condition described there considers only implicitly eliminated variables that have been
officially eliminated from the system. This is not the case for every implicitly eliminated
variable. Consider eliminating `z` from `{x + y + z < 0, x - y - z < 0}`. The result is the set
`{2*x < 0}`; `y` is implicitly but not officially eliminated.

This implementation of Fourier-Motzkin elimination processes variables in decreasing order of
indices. Immediately after a step that eliminates variable `k`, variable `k'` has been eliminated
iff `k' ≥ k`. Thus we can compute the intersection of officially and implicitly eliminated variables
by taking the set of implicitly eliminated variables with indices ≥ `elimed_ge`.
-/
def PComp.maybe_minimal (c : PComp) (elimed_ge : ℕ) : Bool :=
  c.history.size ≤ 1 + ((c.implicit.filter (· ≥ elimed_ge)).union c.effective).size

-- FIXME everything below is just copy-paste from mathlib3

/--
The `src : CompSource` field is ignored when comparing `PComp`s. Two `PComp`s proving the same
comparison, with different sources, are considered equivalent.
-/
def PComp.cmp (p1 p2 : PComp) : Ordering := p1.c.cmp p2.c

/-- `PComp.scale c n` scales the coefficients of `c` by `n` and notes this in the `CompSource`. -/
def PComp.scale (c : PComp) (n : ℕ) : PComp :=
  {c with c := c.c.scale n, src := c.src.scale n}

/--
`PComp.add c1 c2 elim_var` creates the result of summing the linear comparisons `c1` and `c2`,
during the process of eliminating the variable `elim_var`.
The computation assumes, but does not enforce, that `elim_var` appears in both `c1` and `c2`
and does not appear in the sum.
Computing the sum of the two comparisons is easy; the complicated details lie in tracking the
additional fields of `PComp`.
* The historical set `PComp.history` of `c1 + c2` is the union of the two historical sets.
* We recompute the variables that appear in `c1 + c2` from the newly created `Linexp`,
  since some may have been implicitly eliminated.
* The effectively eliminated variables of `c1 + c2` are the union of the two effective sets,
  with `elim_var` inserted.
* The implicitly eliminated variables of `c1 + c2` are those that appear in at least one of
  `c1.vars` and `c2.vars` but not in `(c1 + c2).vars`, excluding `elim_var`.
-/
def PComp.add (c1 c2 : PComp) (elim_var : ℕ) : PComp :=
  let c := c1.c.add c2.c
  let src := c1.src.add c2.src
  let history := c1.history.union c2.history
  let vars := .ofList c.vars
  let effective := (c1.effective.union c2.effective).insert elim_var
  let implicit := ((c1.vars.union c2.vars).sdiff vars).erase elim_var
  ⟨c, src, history, effective, implicit, vars⟩

/--
`PComp.assump c n` creates a `PComp` whose comparison is `c` and whose source is
`CompSource.assump n`, that is, `c` is derived from the `n`th hypothesis.
The history is the singleton set `{n}`.
No variables have been eliminated (effectively or implicitly).
-/
def PComp.assump (c : Comp) (n : ℕ) : PComp :=
{ c := c,
  src := CompSource.assump n,
  history := HashSet.empty.insert n,
  effective := .empty,
  implicit := .empty,
  vars := .ofList c.vars }

instance PComp.ToFormat : ToFormat PComp :=
  ⟨fun p => format p.c.coeffs ++ toString p.c.str ++ "0"⟩

abbrev PCompSet := RBSet PComp PComp.cmp

/-- Creates an empty set of `PComp`s, backed by a red-black map, sorted using `PComp.cmp`.
We use this for performance reasons. -/
-- FIXME inline?
def mkPCompSet : PCompSet := RBSet.empty

/-! ### Elimination procedure -/

/-- If `c1` and `c2` both contain variable `a` with opposite coefficients,
produces `v1` and `v2` such that `a` has been cancelled in `v1*c1 + v2*c2`. -/
def elim_var (c1 c2 : Comp) (a : ℕ) : Option (ℕ × ℕ) :=
let v1 := c1.coeff_of a
let v2 := c2.coeff_of a
if v1 * v2 < 0 then
  let vlcm :=  Nat.lcm v1.natAbs v2.natAbs
  let  v1' := vlcm / v1.natAbs
  let  v2' := vlcm / v2.natAbs
  some ⟨v1', v2'⟩
else none

/--
`pelim_var p1 p2` calls `elim_var` on the `Comp` components of `p1` and `p2`.
If this returns `v1` and `v2`, it creates a new `PComp` equal to `v1*p1 + v2*p2`,
and tracks this in the `CompSource`.
-/
def pelim_var (p1 p2 : PComp) (a : ℕ) : Option PComp := do
  let (n1, n2) ← elim_var p1.c p2.c a
  return (p1.scale n1).add (p2.scale n2) a

/--
A `PComp` represents a contradiction if its `Comp` field represents a contradiction.
-/
def PComp.isContr (p : PComp) : Bool := p.c.isContr

/--
`elim_with_set a p comps` collects the result of calling `pelim_var p p' a`
for every `p' ∈ comps`.
-/
def elim_with_set (a : ℕ) (p : PComp) (comps : PCompSet) : PCompSet :=
comps.foldl (fun s pc =>
match pelim_var p pc a with
| some pc => if pc.maybe_minimal a then s.insert pc else s
| none => s) RBSet.empty

/--
The state for the elimination monad.
* `max_var`: the largest variable index that has not been eliminated.
* `comps`: a set of comparisons

The elimination procedure proceeds by eliminating variable `v` from `comps` progressively
in decreasing order.
-/
structure LinarithData : Type :=
  (max_var : ℕ)
  (comps : PCompSet)

/--
The linarith monad extends an exceptional monad with a `linarith_structure` state.
An exception produces a contradictory `pcomp`.
-/
@[reducible, derive [monad, monad_except pcomp]] meta def linarith_monad : Type → Type :=
state_t linarith_structure (except_t pcomp id)

/-- Returns the current max variable. -/
meta def get_max_var : linarith_monad ℕ :=
linarith_structure.max_var <$> get

/-- Return the current comparison set. -/
meta def get_comps : linarith_monad (rb_set pcomp) :=
linarith_structure.comps <$> get

/-- Throws an exception if a contradictory `pcomp` is contained in the current state. -/
meta def validate : linarith_monad unit :=
do ⟨_, comps⟩ ← get,
match comps.to_list.find (λ p : pcomp, p.is_contr) with
| none := return ()
| some c := throw c
end

/--
Updates the current state with a new max variable and comparisons,
and calls `validate` to check for a contradiction.
-/
meta def update (max_var : ℕ) (comps : rb_set pcomp) : linarith_monad unit :=
state_t.put ⟨max_var, comps⟩ >> validate

/--
`split_set_by_var_sign a comps` partitions the set `comps` into three parts.
* `pos` contains the elements of `comps` in which `a` has a positive coefficient.
* `neg` contains the elements of `comps` in which `a` has a negative coefficient.
* `not_present` contains the elements of `comps` in which `a` has coefficient 0.

Returns `(pos, neg, not_present)`.
-/
meta def split_set_by_var_sign (a : ℕ) (comps : rb_set pcomp) :
  rb_set pcomp × rb_set pcomp × rb_set pcomp :=
comps.fold ⟨mk_pcomp_set, mk_pcomp_set, mk_pcomp_set⟩ $ λ pc ⟨pos, neg, not_present⟩,
  let n := pc.c.coeff_of a in
  if n > 0 then ⟨pos.insert pc, neg, not_present⟩
  else if n < 0 then ⟨pos, neg.insert pc, not_present⟩
  else ⟨pos, neg, not_present.insert pc⟩

/--
`monad.elim_var a` performs one round of Fourier-Motzkin elimination, eliminating the variable `a`
from the `linarith` state.
-/
meta def monad.elim_var (a : ℕ) : linarith_monad unit :=
do vs ← get_max_var,
   when (a ≤ vs) $
do ⟨pos, neg, not_present⟩ ← split_set_by_var_sign a <$> get_comps,
   let cs' := pos.fold not_present (λ p s, s.union (elim_with_set a p neg)),
   update (vs - 1) cs'

/--
`elim_all_vars` eliminates all variables from the linarith state, leaving it with a set of
ground comparisons. If this succeeds without exception, the original `linarith` state is consistent.
-/
meta def elim_all_vars : linarith_monad unit :=
do mv ← get_max_var,
   (list.range $ mv + 1).reverse.mmap' monad.elim_var

/--
`mk_linarith_structure hyps vars` takes a list of hypotheses and the largest variable present in
those hypotheses. It produces an initial state for the elimination monad.
-/
meta def mk_linarith_structure (hyps : list comp) (max_var : ℕ) : linarith_structure :=
let pcomp_list : list pcomp := hyps.enum.map $ λ ⟨n, cmp⟩, pcomp.assump cmp n,
    pcomp_set := rb_set.of_list_core mk_pcomp_set pcomp_list in
⟨max_var, pcomp_set⟩

/--
`produce_certificate hyps vars` tries to derive a contradiction from the comparisons in `hyps`
by eliminating all variables ≤ `max_var`.
If successful, it returns a map `coeff : ℕ → ℕ` as a certificate.
This map represents that we can find a contradiction by taking the sum  `∑ (coeff i) * hyps[i]`.
-/
meta def fourier_motzkin.produce_certificate : certificate_oracle :=
λ hyps max_var,
let state := mk_linarith_structure hyps max_var in
match except_t.run (state_t.run (validate >> elim_all_vars) state) with
| (except.ok (a, _)) := tactic.failed
| (except.error contr) := return contr.src.flatten
end

end linarith
