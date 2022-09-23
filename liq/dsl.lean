import Lean

open Lean Elab Meta

-- enable mapsto `↦` notation
macro x:ident ":" t:term " ↦ " y:term : term => do
`(fun $x : $t => $y)
macro x:ident " ↦ " y:term : term => do
`(fun $x => $y)

namespace Liq

def Symbol := Option String

def Symbol.toString : Symbol → String
| .some s => s
| .none   => "??"

instance : ToString Symbol := ⟨Symbol.toString⟩

instance : Coe String Symbol := ⟨.some⟩

inductive Term
/- bounded variable (de Bruijn index) -/
| bvar (i : Nat)
/- zero symbol -/
| zero
/- addition operator -/
| add (l r : Term)
/- negation operator -/
| neg (r : Term)
/- application of maps -/
| app (f : Symbol) (arg : Term)

inductive Formula
/- equality operator -/
| eq (l r : Term)

structure Sequent := turnstile ::
(context : List Symbol)
(antecedents : List Formula)
(posttext : List Symbol)
(consequents : List Formula)

declare_syntax_cat liq_symbol
syntax "#" term "#" : liq_symbol

partial def elabLIQsymbol : Syntax → TermElabM Expr
| `(liq_symbol| #$s#) => do Term.elabTerm s (← mkAppM ``Liq.Symbol #[])
| _ => throwUnsupportedSyntax

declare_syntax_cat liq_term
syntax ident                 : liq_term
syntax num                   : liq_term
syntax liq_term "+" liq_term : liq_term
syntax          "-" liq_term : liq_term
syntax liq_symbol   liq_term : liq_term

def toNat (s : String) (b : Nat := 10) : Nat :=
s.foldl (a ↦ c ↦ if c.isDigit then b * a + (c.toNat - 48) else a) 0

partial def elabLIQterm : Syntax → TermElabM Expr
| `(liq_term| $i:ident) => mkAppM ``Liq.Term.bvar #[mkNatLit $ toNat i.getId.toString]
| `(liq_term| $_:num)   => mkAppM ``Liq.Term.zero #[]
| `(liq_term| $l + $r) => do
    let l ← elabLIQterm l
    let r ← elabLIQterm r
    mkAppM ``Liq.Term.add #[l, r]
| `(liq_term| - $r) => do
    let r ← elabLIQterm r
    mkAppM ``Liq.Term.neg #[r]
| `(liq_term| $f:liq_symbol $arg:liq_term) => do
    let f ← elabLIQsymbol f
    let arg ← elabLIQterm arg
    mkAppM ``Liq.Term.app #[f, arg]
| _ => throwUnsupportedSyntax

declare_syntax_cat liq_formula
syntax liq_term "=" liq_term : liq_formula

partial def elabLIQformula : Syntax → TermElabM Expr
| `(liq_formula| $l:liq_term = $r:liq_term) => do
    let l ← elabLIQterm l
    let r ← elabLIQterm r
    mkAppM ``Liq.Formula.eq #[l, r]
| _ => throwUnsupportedSyntax

declare_syntax_cat liq_sequent
syntax "∀" liq_symbol* liq_formula* "⊢" "∃" liq_symbol* liq_formula* : liq_sequent

def _root_.Lean.Expr.mkList (ty : Expr) : List Expr → MetaM Expr
| []        => mkAppOptM ``List.nil #[ty]
| (e :: es) => do mkAppM ``List.cons #[e, (← mkList ty es)]

partial def elabLIQsequent : Syntax → TermElabM Expr
| `(liq_sequent| ∀ $S₁:liq_symbol* $Γ:liq_formula* ⊢ ∃ $S₂:liq_symbol* $P:liq_formula*) => do
    let S₁ ← S₁.mapM elabLIQsymbol  >>= L ↦ Expr.mkList (.const ``Symbol []) L.toList
    let Γ  ←  Γ.mapM elabLIQformula >>= L ↦ Expr.mkList (.const ``Formula []) L.toList
    let S₂ ← S₂.mapM elabLIQsymbol  >>= L ↦ Expr.mkList (.const ``Symbol []) L.toList
    let P  ←  P.mapM elabLIQformula >>= L ↦ Expr.mkList (.const ``Formula []) L.toList
    mkAppM ``Liq.Sequent.turnstile #[S₁, Γ, S₂, P]
| _ => throwUnsupportedSyntax

elab t:liq_sequent : term => elabLIQsequent t

def exact (A d1 B d2 : Symbol) : Sequent :=
∀ #B#
#d2# x0 = 0
⊢
∃ #A#
#d1# y0 = x1

def inj (A f : Symbol) : Sequent :=
∀ #A#
#f# x0 = 0
⊢
∃
x0 = 0


#reduce exact "V^{i-1}" "d" "V^i" "d"


infix:0 "========================================" => Prod.mk

def snake2 : (List Expr) × Expr :=
[ exact "A₀" "d" "B₀" "d",
  exact "A₁" "d" "B₁" "d",
  exact "A₂" "d" "B₂" "d",
  exact "0" "d'" "A₀" "d'",
  exact "A₀" "d'" "A₁" "d'",
  exact "A₁" "d'" "A₂" "d'",
  exact "0" "d'" "C₀" "d'",
  exact "C₀" "d'" "C₁" "d'",
  exact "C₁" "d'" "C₂" "d'" ]
========================================
.and (exact "0" "d'" "B₀" "d'") $
.and (exact "B₀" "d'" "B₁" "d'") $
     (exact "B₁" "d'" "B₂" "d'")

protected def Expr.toString (Γ : List Name := []) : Expr → String -- `Γ` = context
| .bvar i => Name.toString $ (Γ.get? i).map Name.toString
| .forall name ty body => let B := body.toString (name :: Γ); s!"∀ {name} ∈ {ty}, {B}"
| .exists name ty body => let B := body.toString (name :: Γ); s!"∃ {name} ∈ {ty}, {B}"
| .imp left right => let L := left.toString Γ; let R := right.toString Γ; s!"{L} → {R}"
| .and left right => let L := left.toString Γ; let R := right.toString Γ; s!"{L} ∧ {R}"
| .eq  left right => let L := left.toString Γ; let R := right.toString Γ; s!"{L} = {R}"
| .add left right => let L := left.toString Γ; let R := right.toString Γ; s!"{L} + {R}"
| .neg right => let R := right.toString Γ; s!"-{R}"
| .zero => "0"
| .app name input => let I := input.toString Γ; s!"{name} {I}"

#eval (exact "V^{i-1}" "d" "V^i" "d").toString

def next : StateM Nat Nat := do
  let x ← get
  modify (.+1)
  pure x

def Expr.interpretNormy (e : Expr) : StateM Nat String :=
IP [] e -- `IP` = interpreter
where
IP (Γ : List Name := []) : Expr → StateM Nat String -- `Γ` = context
| .bvar i => pure (Name.toString $ (Γ.get? i).map Name.toString)
| .forall name ty body => IP (name :: Γ) body >>= B ↦ pure s!"⨆ {name} ∈ {ty}, {B}"
| .exists name ty body => IP (name :: Γ) body >>= B ↦ pure s!"⨅ {name} ∈ {ty}, {B}"
| .imp left right => do
    let L ← IP Γ left
    let n ← next
    let R ← IP Γ right
    pure s!"{R} - K_{n} * {L}"
| .and left right => do
    let L ← IP Γ left
    let n₁ ← next
    let n₂ ← next
    let R ← IP Γ right
    pure s!"K_{n₁} * {L} + K_{n₂} * {R}"
| .eq  left right => IP Γ left >>= L ↦ IP Γ right >>= R ↦ pure s!"∥{L} - {R}∥"
| .add left right => IP Γ left >>= L ↦ IP Γ right >>= R ↦ pure s!"{L} + {R}"
| .neg right      =>                   IP Γ right >>= R ↦ pure s!"-{R}"
| .zero           =>                                      pure "0"
| .app name input => IP Γ input >>=                   I ↦ pure s!"{name} {I}"

#eval (exact "V^{i-1}" "d" "V^i" "d").interpretNormy 0

#eval snake2.interpretNormy

def Expr.interpretSheafy (e : Expr) : String :=
postprocess $ IP [] e 0 -- `IP` = interpreter
where
postprocess (expr : String × Nat) : String :=
  let pre : String := String.join $ (List.range expr.2).map fun i => s!"∃ k_{i}, "
  pre ++ expr.1
IP (Γ : List Name := []) : Expr → StateM Nat String -- `Γ` = context
| .bvar i => let N := Name.toString $ (Γ.get? i).map Name.toString
    pure (if i = 0 then N else s!"res({N})")
| .forall name ty body => do
    let B ← IP (name :: Γ) body
    pure s!"∀ c ≫ 0, {name} ∈ {ty} c, {B}"
| .exists name ty body => do
    let B ← IP (name :: Γ) body
    let n ← next
    pure s!"∃ {name} ∈ {ty} (c / k_{n}), {B}"
| .imp left right => do pure s!"{(← IP Γ left)} → {(← IP Γ right)}"
| .and left right => IP Γ left >>= L ↦ IP Γ right >>= R ↦ pure s!"{L} ∧ {R}"
| .eq  left right => IP Γ left >>= L ↦ IP Γ right >>= R ↦ pure s!"{L} = {R}"
| .add left right => IP Γ left >>= L ↦ IP Γ right >>= R ↦ pure s!"{L} + {R}"
| .neg right      =>                   IP Γ right >>= R ↦ pure s!"-{R}"
| .zero           =>                                      pure "0"
| .app name input => IP Γ input >>=                   I ↦ pure s!"{name} {I}"

#eval (exact "V^{i-1}" "d" "V^i" "d").interpretSheafy

end Liq
