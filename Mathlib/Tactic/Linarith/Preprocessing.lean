/-
Copyright (c) 2020 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
import Mathlib.Tactic.Linarith.Datatypes
-- import Mathlib.Tactic.CancelDenoms
-- import Mathlib.Tactic.Zify

/-!
# Linarith preprocessing

This file contains methods used to preprocess inputs to `linarith`.

In particular, `linarith` works over comparisons of the form `t R 0`, where `R ∈ {<,≤,=}`.
It assumes that expressions in `t` have integer coefficients and that the type of `t` has
well-behaved subtraction.

## Implementation details

A `GlobalPreprocessor` is a function `List Expr → TacticM (List Expr)`. Users can add custom
preprocessing steps by adding them to the `LinarithConfig` object. `Linarith.defaultPreprocessors`
is the main list, and generally none of these should be skipped unless you know what you're doing.
-/

namespace Linarith

/-! ### Preprocessing -/

open Lean Elab Tactic Meta
open Qq

/--
If `prf` is a proof of `¬ e`, where `e` is a comparison,
`rem_neg prf e` flips the comparison in `e` and returns a proof.
For example, if `prf : ¬ a < b`, ``rem_neg prf `(a < b)`` returns a proof of `a ≥ b`.
-/
def rem_neg (prf : Expr) (e : Expr) : MetaM Expr :=
  match e.getAppFnArgs with
  | (``LE.le, #[_, _, _, _]) => mkAppM ``lt_of_not_ge #[prf]
  | (``LT.lt, #[_, _, _, _]) => mkAppM ``le_of_not_gt #[prf]
  | (``GT.gt, #[_, _, _, _]) => mkAppM ``le_of_not_gt #[prf]
  | (``GE.ge, #[_, _, _, _]) => mkAppM ``lt_of_not_ge #[prf]
  | _ => throwError "Not a comparison"

partial def rearr_comp_aux (proof e : Expr) : MetaM Expr :=
  match e.getAppFnArgs with
  | (``LE.le, #[_, _, a, b]) => match a.getAppFnArgs, b.getAppFnArgs with
    | _, (``OfNat.ofNat, #[_, .lit (.natVal 0), _]) => return proof
    | (``OfNat.ofNat, #[_, .lit (.natVal 0), _]), _ => mkAppM ``neg_nonpos_of_nonneg #[proof]
    | _, _                                          => mkAppM ``sub_nonpos_of_le #[proof]
  | (``LT.lt, #[_, _, a, b]) => match a.getAppFnArgs, b.getAppFnArgs with
    | _, (``OfNat.ofNat, #[_, .lit (.natVal 0), _]) => return proof
    | (``OfNat.ofNat, #[_, .lit (.natVal 0), _]), _ => mkAppM ``neg_neg_of_pos #[proof]
    | _, _                                          => mkAppM ``sub_neg_of_lt #[proof]
  | (``Eq, #[_, a, b]) => match a.getAppFnArgs, b.getAppFnArgs with
    | _, (``OfNat.ofNat, #[_, .lit (.natVal 0), _]) => return proof
    | (``OfNat.ofNat, #[_, .lit (.natVal 0), _]), _ => mkAppM ``Eq.symm #[proof]
    | _, _                                          => mkAppM ``sub_eq_zero_of_eq #[proof]
  | (``GT.gt, #[_, _, a, b]) => match a.getAppFnArgs, b.getAppFnArgs with
    | _, (``OfNat.ofNat, #[_, .lit (.natVal 0), _]) => mkAppM ``neg_neg_of_pos #[proof]
    | (``OfNat.ofNat, #[_, .lit (.natVal 0), _]), _ => mkAppM ``lt_zero_of_zero_gt #[proof]
    | _, _                                          => mkAppM ``sub_neg_of_lt #[proof]
  | (``GE.ge, #[_, _, a, b]) => match a.getAppFnArgs, b.getAppFnArgs with
    | _, (``OfNat.ofNat, #[_, .lit (.natVal 0), _]) => mkAppM ``neg_nonpos_of_nonneg #[proof]
    | (``OfNat.ofNat, #[_, .lit (.natVal 0), _]), _ => mkAppM ``le_zero_of_zero_ge #[proof]
    | _, _                                          => mkAppM ``sub_nonpos_of_le #[proof]
  | (``Not, #[a]) => do
    let nproof ← rem_neg proof a
    rearr_comp_aux nproof (← inferType nproof)
  | a => throwError m!"couldn't rearrange comp {a}"

/--
`rearr_comp e` takes a proof `e` of an equality, inequality, or negation thereof,
and turns it into a proof of a comparison `_ R 0`, where `R ∈ {=, ≤, <}`.
 -/
def rearr_comp (e : Expr) : MetaM Expr := do
  rearr_comp_aux e (← instantiateMVars (← inferType e))

/-- If `e` is of the form `((n : ℕ) : ℤ)`, `is_nat_int_coe e` returns `n : ℕ`. -/
def is_nat_int_coe (e : Expr) : Option Expr :=
  match e.getAppFnArgs with
  | (``Nat.cast, #[.const ``Int [], _, n]) => some n
  | _ => none

/-- If `e : ℕ`, returns a proof of `0 ≤ (e : ℤ)`. -/
def mk_coe_nat_nonneg_prf (e : Expr) : MetaM Expr :=
mkAppM `int.coe_nat_nonneg #[e]

/-- `get_nat_comps e` returns a list of all subexpressions of `e` of the form `((t : ℕ) : ℤ)`. -/
partial def get_nat_comps (e : Expr) : List Expr :=
  match is_nat_int_coe e with
  | some n => [n]
  | none => match e.getAppFnArgs with
    | (``HAdd.hAdd, #[_, _, _, _, a, b]) => get_nat_comps a ++ get_nat_comps b
    | (``HMul.hMul, #[_, _, _, _, a, b]) => get_nat_comps a ++ get_nat_comps b
    | _ => []

/--
If `pf` is a proof of a strict inequality `(a : ℤ) < b`,
`mk_non_strict_int_pf_of_strict_int_pf pf` returns a proof of `a + 1 ≤ b`,
and similarly if `pf` proves a negated weak inequality.
-/
def mk_non_strict_int_pf_of_strict_int_pf (pf : Expr) : MetaM Expr := do
  match (← inferType pf).getAppFnArgs with
  | (``LT.lt, #[_, _, _, _]) => return mkApp (← mkAppM ``Iff.mpr #[← mkAppOptM ``Int.add_one_le_iff #[none, none]]) pf
  | (``GT.gt, #[_, _, _, _]) => return mkApp (← mkAppM ``Iff.mpr #[← mkAppOptM ``Int.add_one_le_iff #[none, none]]) pf
  | (``Not, #[P]) => match P.getAppFnArgs with
    | (``LE.le, #[_, _, _, _]) => return mkApp (← mkAppM ``Iff.mpr #[← mkAppOptM ``Int.add_one_le_iff #[none, none]]) (← mkAppM `le_of_not_gt #[pf])
    | (``GE.ge, #[_, _, _, _]) => return mkApp (← mkAppM ``Iff.mpr #[← mkAppOptM ``Int.add_one_le_iff #[none, none]]) (← mkAppM `le_of_not_gt #[pf])
    | _ => throwError "mk_non_strict_int_pf_of_strict_int_pf failed: proof is not an inequality"
  | _ => throwError "mk_non_strict_int_pf_of_strict_int_pf failed: proof is not an inequality"

/--
`is_nat_prop tp` is true iff `tp` is an inequality or equality between natural numbers
or the negation thereof.
-/
partial def is_nat_prop (e : Expr) : Bool :=
  match e.getAppFnArgs with
  | (``Eq, #[.const ``Nat [], _, _]) => true
  | (``LE.le, #[.const ``Nat [], _, _, _]) => true
  | (``LT.lt, #[.const ``Nat [], _, _, _]) => true
  | (``GE.ge, #[.const ``Nat [], _, _, _]) => true
  | (``GT.gt, #[.const ``Nat [], _, _, _]) => true
  | (``Not, #[e]) => is_nat_prop e
  | _ => false

/--
`is_strict_int_prop tp` is true iff `tp` is a strict inequality between integers
or the negation of a weak inequality between integers.
-/
def is_strict_int_prop (e : Expr) : Bool :=
  match e.getAppFnArgs with
  | (``LT.lt, #[.const ``Int [], _, _, _]) => true
  | (``GT.gt, #[.const ``Int [], _, _, _]) => true
  | (``Not, #[e]) => match e.getAppFnArgs with
    | (``LE.le, #[.const ``Int [], _, _, _]) => true
    | (``GE.ge, #[.const ``Int [], _, _, _]) => true
    | _ => false
  | _ => false

partial def filter_comparisons_aux (e : Expr) : Bool :=
  match e.getAppFnArgs with
  | (``Eq, _) => true
  | (``LE.le, _) => true
  | (``LT.lt, _) => true
  | (``GE.ge, _) => true
  | (``GT.gt, _) => true
  | (``Not, #[e]) => filter_comparisons_aux e -- TODO hmm, this lets `¬ ¬ a ≤ b` through, but we probably can't handle that
  | _ => false

/--
Removes any expressions that are not proofs of inequalities, equalities, or negations thereof.
-/
def filter_comparisons : Preprocessor :=
{ name := "filter terms that are not proofs of comparisons",
  transform := fun h => do
   let tp ← instantiateMVars (← inferType h)
   if (← isProp tp) && filter_comparisons_aux tp then return [h]
   else return [] }

/--
Replaces proofs of negations of comparisons with proofs of the reversed comparisons.
For example, a proof of `¬ a < b` will become a proof of `a ≥ b`.
-/
def remove_negations : Preprocessor :=
{ name := "replace negations of comparisons",
  transform := fun h => do
    let t : Q(Prop) ← inferType h
    match t with
    | ~q(¬ $p) => return [← rem_neg h p]
    | _        => return [h] }


-- FIXME the `nat_to_int : GlobalPreprocessor` from mathlib3 will need to wait for a port of `zify`.
-- /--
-- If `h` is an equality or inequality between natural numbers,
-- `nat_to_int` lifts this inequality to the integers.
-- It also adds the facts that the integers involved are nonnegative.
-- To avoid adding the same nonnegativity facts many times, it is a global preprocessor.
--  -/
-- meta def nat_to_int : global_preprocessor :=
-- { name := "move nats to ints",
--   transform := λ l,
-- -- we lock the tactic state here because a `simplify` call inside of
-- -- `zify_proof` corrupts the tactic state when run under `io.run_tactic`.
-- do l ← lock_tactic_state $ l.mmap $ λ h,
--          infer_type h >>= guardb ∘ is_nat_prop >> zify_proof [] h <|> return h,
--    nonnegs ← l.mfoldl (λ (es : expr_set) h, do
--      (a, b) ← infer_type h >>= get_rel_sides,
--      return $ (es.insert_list (get_nat_comps a)).insert_list (get_nat_comps b)) mk_rb_set,
--    (++) l <$> nonnegs.to_list.mmap mk_coe_nat_nonneg_prf }


/-- `strengthen_strict_int h` turns a proof `h` of a strict integer inequality `t1 < t2`
into a proof of `t1 ≤ t2 + 1`. -/
def strengthen_strict_int : Preprocessor :=
{ name := "strengthen strict inequalities over int",
  transform := fun h => do
    if is_strict_int_prop (← inferType h) then
      return [← mk_non_strict_int_pf_of_strict_int_pf h]
    else
      return [h] }

/--
`mk_comp_with_zero h` takes a proof `h` of an equality, inequality, or negation thereof,
and turns it into a proof of a comparison `_ R 0`, where `R ∈ {=, ≤, <}`.
 -/
def make_comp_with_zero : Preprocessor :=
{ name := "make comparisons with zero",
  transform := fun e =>
  return [← rearr_comp e]
  -- do try return [← rearr_comp e] catch _ => return []
  }

-- FIXME the `cancel_denoms : Preprocessor` from mathlib3 will need to wait
-- for a port of the `cancel_denoms` tactic.
-- /--
-- `normalize_denominators_in_lhs h lhs` assumes that `h` is a proof of `lhs R 0`.
-- It creates a proof of `lhs' R 0`, where all numeric division in `lhs` has been cancelled.
-- -/
-- meta def normalize_denominators_in_lhs (h lhs : expr) : tactic expr :=
-- do (v, lhs') ← cancel_factors.derive lhs,
--    if v = 1 then return h else do
--    (ih, h'') ← mk_single_comp_zero_pf v h,
--    (_, nep, _) ← infer_type h'' >>= rewrite_core lhs',
--    mk_eq_mp nep h''

-- /--
-- `cancel_denoms pf` assumes `pf` is a proof of `t R 0`. If `t` contains the division symbol `/`,
-- it tries to scale `t` to cancel out division by numerals.
-- -/
-- meta def cancel_denoms : preprocessor :=
-- { name := "cancel denominators",
--   transform := λ pf,
-- (do some (_, lhs) ← parse_into_comp_and_expr <$> infer_type pf,
--    guardb $ lhs.contains_constant (= `has_div.div),
--    singleton <$> normalize_denominators_in_lhs pf lhs)
-- <|> return [pf] }


-- FIXME `nlinarith` can wait for later
-- /--
-- `find_squares m e` collects all terms of the form `a ^ 2` and `a * a` that appear in `e`
-- and adds them to the set `m`.
-- A pair `(a, tt)` is added to `m` when `a^2` appears in `e`, and `(a, ff)` is added to `m`
-- when `a*a` appears in `e`.  -/
-- meta def find_squares : rb_set (expr × bool) → expr → tactic (rb_set $ expr ×ₗ bool)
-- | s `(%%a ^ 2) := do s ← find_squares s a, return (s.insert (a, tt))
-- | s e@`(%%e1 * %%e2) := if e1 = e2 then do s ← find_squares s e1, return (s.insert (e1, ff)) else
--   e.mfoldl find_squares s
-- | s e := e.mfoldl find_squares s

-- /--
-- `nlinarith_extras` is the preprocessor corresponding to the `nlinarith` tactic.

-- * For every term `t` such that `t^2` or `t*t` appears in the input, adds a proof of `t^2 ≥ 0`
--   or `t*t ≥ 0`.
-- * For every pair of comparisons `t1 R1 0` and `t2 R2 0`, adds a proof of `t1*t2 R 0`.

-- This preprocessor is typically run last, after all inputs have been canonized.
-- -/
-- meta def nlinarith_extras : global_preprocessor :=
-- { name := "nonlinear arithmetic extras",
--   transform := λ ls,
-- do s ← ls.mfoldr (λ h s', infer_type h >>= find_squares s') mk_rb_set,
--    new_es ← s.mfold ([] : list expr) $ λ ⟨e, is_sq⟩ new_es,
--      ((do p ← mk_app (if is_sq then ``sq_nonneg else ``mul_self_nonneg) [e],
--        return $ p::new_es) <|> return new_es),
--    new_es ← make_comp_with_zero.globalize.transform new_es,
--    linarith_trace "nlinarith preprocessing found squares",
--    linarith_trace s,
--    linarith_trace_proofs "so we added proofs" new_es,
--    with_comps ← (new_es ++ ls).mmap (λ e, do
--      tp ← infer_type e,
--      return $ (parse_into_comp_and_expr tp).elim (ineq.lt, e) (λ ⟨ine, _⟩, (ine, e))),
--    products ← with_comps.mmap_upper_triangle $ λ ⟨posa, a⟩ ⟨posb, b⟩,
--      some <$> match posa, posb with
--       | ineq.eq, _ := mk_app ``zero_mul_eq [a, b]
--       | _, ineq.eq := mk_app ``mul_zero_eq [a, b]
--       | ineq.lt, ineq.lt := mk_app ``mul_pos_of_neg_of_neg [a, b]
--       | ineq.lt, ineq.le := do a ← mk_app ``le_of_lt [a],
--         mk_app ``mul_nonneg_of_nonpos_of_nonpos [a, b]
--       | ineq.le, ineq.lt := do b ← mk_app ``le_of_lt [b],
--         mk_app ``mul_nonneg_of_nonpos_of_nonpos [a, b]
--       | ineq.le, ineq.le := mk_app ``mul_nonneg_of_nonpos_of_nonpos [a, b]
--       end <|> return none,
--    products ← make_comp_with_zero.globalize.transform products.reduce_option,
--    return $ new_es ++ ls ++ products }

-- FIXME the `remove_ne` preprocesor
-- /--
-- `remove_ne_aux` case splits on any proof `h : a ≠ b` in the input, turning it into `a < b ∨ a > b`.
-- This produces `2^n` branches when there are `n` such hypotheses in the input.
-- -/
-- meta def remove_ne_aux : list expr → tactic (list branch) :=
-- λ hs,
-- (do e ← hs.mfind (λ e : expr, do e ← infer_type e, guard $ e.is_ne.is_some),
--     [(_, ng1), (_, ng2)] ← to_expr ``(or.elim (lt_or_gt_of_ne %%e)) >>= apply,
--     let do_goal : expr → tactic (list branch) := λ g,
--       do set_goals [g],
--          h ← intro1,
--          ls ← remove_ne_aux $ hs.remove_all [e],
--          return $ ls.map (λ b : branch, (b.1, h::b.2)) in
--     (++) <$> do_goal ng1 <*> do_goal ng2)
-- <|> do g ← get_goal, return [(g, hs)]

-- /--
-- `remove_ne` case splits on any proof `h : a ≠ b` in the input, turning it into `a < b ∨ a > b`,
-- by calling `linarith.remove_ne_aux`.
-- This produces `2^n` branches when there are `n` such hypotheses in the input.
-- -/
-- meta def remove_ne : global_branching_preprocessor :=
-- { name := "remove_ne",
--   transform := remove_ne_aux }

/--
The default list of preprocessors, in the order they should typically run.
-/
def default_preprocessors : List GlobalBranchingPreprocessor :=
[filter_comparisons, remove_negations/-, nat_to_int-/, strengthen_strict_int,
  make_comp_with_zero/-, cancel_denoms-/]

/--
`preprocess pps l` takes a list `l` of proofs of propositions.
It maps each preprocessor `pp ∈ pps` over this list.
The preprocessors are run sequentially: each receives the output of the previous one.
Note that a preprocessor may produce multiple or no expressions from each input expression,
so the size of the list may change.
-/
def preprocess (pps : List GlobalBranchingPreprocessor) (g : MVarId) (l : List Expr) :
    MetaM (List Branch) := do
  pps.foldlM (fun ls pp =>
    List.join <$> (ls.mapM $ fun b => do pp.process b.1 b.2))
    [(g, l)]

end Linarith