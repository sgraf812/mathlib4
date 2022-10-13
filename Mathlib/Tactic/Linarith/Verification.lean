/-
Copyright (c) 2020 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/

import Mathlib.Tactic.Linarith.Elimination
import Mathlib.Tactic.Linarith.Parsing

/-!
# Deriving a proof of false

`linarith` uses an untrusted oracle to produce a certificate of unsatisfiability.
It needs to do some proof reconstruction work to turn this into a proof term.
This file implements the reconstruction.

## Main declarations

The public facing declaration in this file is `proveFalseByLinarith`.
-/

namespace Qq

def ofNatQ (α : Q(Type $u)) (_ : Q(Semiring $α)) (n : ℕ) : Q($α) :=
  have : Q(OfNat $α $n) := match n with
  | 0 => (q(inferInstance) : Q(OfNat $α (nat_lit 0)))
  | 1 => (q(inferInstance) : Q(OfNat $α (nat_lit 1)))
  | _+2 => q(inferInstance)
  q(OfNat.ofNat $n)

end Qq

namespace Linarith

open Ineq Lean Elab Tactic Meta

/-! ### Auxiliary functions for assembling proofs -/

open Qq

/-- A typesafe version of `mulExpr`. -/
def mulExpr' (n : ℕ) {α : Q(Type $u)} (inst : Q(Semiring $α)) (e : Q($α)) : Q($α) :=
if n = 1 then e else
  let n := ofNatQ α inst n
  q($n * $e)

/--
`mulExpr n e` creates an `Expr` representing `n*e`.
When elaborated, the coefficient will be a native numeral of the same type as `e`.
-/
def mulExpr (n : ℕ) (e : Expr) : MetaM Expr := do
  let ⟨u, α, e⟩ ← inferTypeQ' e
  let inst : Q(Semiring $α) ← synthInstanceQ q(Semiring $α)
  return mulExpr' n inst e

/-- A type-safe analogue of `addExprs`. -/
def addExprs' {α : Q(Type $u)} (inst : Q(AddMonoid $α)) : List Q($α) → Q($α)
| []   => q(0)
| [a]  => a
| h::t => let t := addExprs' inst t; q($h + $t)

/-- `addExprs L` creates an `Expr` representing the sum of the elements of `L`, associated right. -/
-- FIXME does it actually matter that we associate right? In mathlib3 we associate left.
def addExprs : List Expr → MetaM Expr
| [] => return q(0) -- This may not be of the intended type; use with caution.
| L@(h::_) => do
  let ⟨u, α, _⟩ ← inferTypeQ' h
  let inst : Q(AddMonoid $α) ← synthInstanceQ q(AddMonoid $α)
  -- This is not type safe; we just assume all the `Expr`s in the tail have the same type:
  return addExprs' inst L

/--
If our goal is to add together two inequalities `t1 R1 0` and `t2 R2 0`,
`ineq_const_nm R1 R2` produces the strength of the inequality in the sum `R`,
along with the name of a lemma to apply in order to conclude `t1 + t2 R 0`.
-/
def ineq_const_nm : Ineq → Ineq → (Name × Ineq)
| eq, eq => (`eq_of_eq_of_eq, eq)
| eq, le => (``le_of_eq_of_le, le)
| eq, lt => (``lt_of_eq_of_lt, lt)
| le, eq => (``le_of_le_of_eq, le)
| le, le => (`add_nonpos, le)
| le, lt => (`add_lt_of_le_of_neg, lt)
| lt, eq => (``lt_of_lt_of_eq, lt)
| lt, le => (`add_lt_of_neg_of_le, lt)
| lt, lt => (`left.add_neg, lt)

/--
`mk_lt_zero_pf_aux c pf npf coeff` assumes that `pf` is a proof of `t1 R1 0` and `npf` is a proof
of `t2 R2 0`. It uses `mk_single_comp_zero_pf` to prove `t1 + coeff*t2 R 0`, and returns `R`
along with this proof.
-/
def mk_lt_zero_pf_aux (c : Ineq) (pf npf : Expr) (coeff : ℕ) : TermElabM (Ineq × Expr) := do
  let (iq, h') ← mkSingleCompZeroOf coeff npf
  let (nm, niq) := ineq_const_nm c iq
  return (niq, ←mkAppM nm #[pf, h'])

/--
`mk_lt_zero_pf coeffs pfs` takes a list of proofs of the form `tᵢ Rᵢ 0`,
paired with coefficients `cᵢ`.
It produces a proof that `∑cᵢ * tᵢ R 0`, where `R` is as strong as possible.
-/
def mk_lt_zero_pf : List (Expr × ℕ) → TermElabM Expr
| [] => throwError "no linear hypotheses found"
| [(h, c)] => do
     let (_, t) ← mkSingleCompZeroOf c h
     return t
| ((h, c)::t) => do
     let (iq, h') ← mkSingleCompZeroOf c h
     let (_, t) ← t.foldlM (λ pr ce => mk_lt_zero_pf_aux pr.1 pr.2 ce.1 ce.2) (iq, h')
     return t

/-- If `prf` is a proof of `t R s`, `term_of_ineq_prf prf` returns `t`. -/
def term_of_ineq_prf (prf : Expr) : MetaM Expr := do
  let (t, _) ← getRelSides (← inferType prf)
  return t

/-- If `prf` is a proof of `t R s`, `ineq_prf_tp prf` returns the type of `t`. -/
def ineq_prf_tp (prf : Expr) : MetaM Expr := do
  inferType (← term_of_ineq_prf prf)

/--
`mk_neg_one_lt_zero_pf tp` returns a proof of `-1 < 0`,
where the numerals are natively of type `tp`.
-/
def mk_neg_one_lt_zero_pf (tp : Expr) : MetaM Expr := do
  let zero_lt_one ← mkAppOptM `zero_lt_one #[tp, none, none]
  mkAppM `neg_neg_of_pos #[zero_lt_one]

/--
If `e` is a proof that `t = 0`, `mk_neg_eq_zero_pf e` returns a proof that `-t = 0`.
-/
def mk_neg_eq_zero_pf (e : Expr) : MetaM Expr := do
  return mkAppN (← mkAppM `Iff.mpr #[mkConst `neg_eq_zero]) #[e]

/--
`prove_eq_zero_using tac e` tries to use `tac` to construct a proof of `e = 0`.
-/
def prove_eq_zero_using (tac : TacticM Unit) (e : Expr) : TermElabM Expr := do
  let ⟨u, α, e⟩ ← inferTypeQ' e
  let _h : Q(Zero $α) ← synthInstanceQ q(Zero $α)
  synthesizeUsing q($e = 0) tac

/--
`add_neg_eq_pfs l` inspects the list of proofs `l` for proofs of the form `t = 0`. For each such
proof, it adds a proof of `-t = 0` to the list.
-/
def add_neg_eq_pfs : List Expr → MetaM (List Expr)
| [] => return []
| (h::t) => do
  let (iq, _) ← parseCompAndExpr (← inferType h)
  match iq with
  | Ineq.eq => do
    let nep ← mk_neg_eq_zero_pf h
    let tl ← add_neg_eq_pfs t
    return h::nep::tl
  | _ => return h :: (← add_neg_eq_pfs t)

/-! #### The main method -/

/--
`proveFalseByLinarith` is the main workhorse of `linarith`.
Given a list `l` of proofs of `tᵢ Rᵢ 0`,
it tries to derive a contradiction from `l` and use this to produce a proof of `False`.

An oracle is used to search for a certificate of unsatisfiability.
In the current implementation, this is the Fourier Motzkin elimination routine in
`Elimination.lean`, but other oracles could easily be swapped in.

The returned certificate is a map `m` from hypothesis indices to natural number coefficients.
If our set of hypotheses has the form  `{tᵢ Rᵢ 0}`,
then the elimination process should have guaranteed that
1.\ `∑ (m i)*tᵢ = 0`,
with at least one `i` such that `m i > 0` and `Rᵢ` is `<`.

We have also that
2.\ `∑ (m i)*tᵢ < 0`,
since for each `i`, `(m i)*tᵢ ≤ 0` and at least one is strictly negative.
So we conclude a contradiction `0 < 0`.

It remains to produce proofs of (1) and (2). (1) is verified by calling the `discharger` tactic
of the `LinarithConfig` object, which is typically `ring`. We prove (2) by folding over the
set of hypotheses.
-/
def proveFalseByLinarith (cfg : LinarithConfig) : MVarId → List Expr → TermElabM Expr
| _, [] => throwError "no args to linarith"
| g, l@(h::_) => do
    -- for the elimination to work properly, we must add a proof of `-1 < 0` to the list,
    -- along with negated equality proofs.
    logInfo m!"waking up in proveFalseByLinarith with {l}"
    -- let l' ← add_neg_eq_pfs l
    -- let hz ← mk_neg_one_lt_zero_pf (← ineq_prf_tp h)
    -- let inputs := hz::l'
    -- -- perform the elimination and fail if no contradiction is found.
    -- let (comps, max_var) ← linearFormsAndMaxVar cfg.transparency inputs
    -- logInfo m!"{comps}"
    -- logInfo m!"{max_var}"
    -- let oracle := cfg.oracle.getD FourierMotzkin.produceCertificate
    throwError "hello world"
    -- let certificate : Std.HashMap Nat Nat ← oracle comps max_var
    --   <|> throwError "linarith failed to find a contradiction"
    -- linarithTrace "linarith has found a contradiction"
    -- let enum_inputs := inputs.enum
    -- -- construct a list pairing nonzero coeffs with the proof of their corresponding comparison
    -- let zip := enum_inputs.filterMap (fun ⟨n, e⟩ => (certificate.find? n).map (e, ·))
    -- let mls ← zip.mapM (fun ⟨e, n⟩ => do mulExpr n (← term_of_ineq_prf e))
    -- -- `sm` is the sum of input terms, scaled to cancel out all variables.
    -- let sm ← addExprs mls -- FIXME there was a to_expr here previously
    -- linarithTrace "The expression\n  {sm}\nshould be both 0 and negative"
    -- -- we prove that `sm = 0`, typically with `ring`.
    -- let sm_eq_zero ← prove_eq_zero_using cfg.discharger sm
    -- linarithTrace "We have proved that it is zero"
    -- -- we also prove that `sm < 0`.
    -- let sm_lt_zero ← mk_lt_zero_pf zip
    -- linarithTrace "We have proved that it is negative"
    -- -- this is a contradiction.
    -- let pftp ← inferType sm_lt_zero
    -- let ⟨_, nep, _⟩ ← g.rewrite sm_eq_zero pftp
    -- let pf' ← mkAppM ``Eq.mp #[nep, sm_lt_zero]
    -- mkAppM `lt_irrefl #[pf']

end Linarith
