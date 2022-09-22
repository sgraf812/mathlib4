import Lean

open Lean

namespace Liq

def Name := Option String

def Name.toString : Name → String
| .some s => s
| .none   => "??"

instance : ToString Name := ⟨Name.toString⟩

instance : Coe String Name := ⟨.some⟩

inductive Expr
/- bounded variable (de Bruijn index) -/
| bvar (i : Nat)
/- universal quantifier -/
| forall (name : Name) (ty : Name) (body : Expr)
/- existential quantifier -/
| exists (name : Name) (ty : Name) (body : Expr)
/- implication connector -/
| implies (left right : Expr)
/- conjunction connector -/
| and (left right : Expr)
/- equality operator -/
| eq (left right : Expr)
/- addition operator -/
| add (left right : Expr)
/- negation operator -/
| neg (right : Expr)
/- zero symbol -/
| zero
/- application of maps -/
| app (name : Name) (input : Expr)

def exact : Expr :=
.forall "x" "V^i" $
  .implies
    (.eq (.app "d" $ .bvar 0) .zero) $
    .exists "y" "V^{i-1}" $
      .eq (.app "d" $ .bvar 0) (.bvar 1)

-- declare_syntax_cat liq
-- syntax "∀ "       : liq
-- -- syntax "+"       : liq
-- -- syntax "="       : liq

-- def elabExpr : Syntax → MetaM Lean.Expr
-- | `(liq| "∀ ") => _


protected def Expr.toString (ctx : List Name := []) : Expr → String
| .bvar i => Name.toString $ (ctx.get? i).map Name.toString
| .forall name ty body =>
    "∀ " ++ name.toString ++ " ∈ " ++ ty.toString ++ ", " ++ body.toString (name :: ctx)
| .exists name ty body =>
    "∃ " ++ name.toString ++ " ∈ " ++ ty.toString ++ ", " ++ body.toString (name :: ctx)
| .implies left right => left.toString ctx ++ " → " ++ right.toString ctx
| .and left right => left.toString ctx ++ " ∧ " ++ right.toString ctx
| .eq left right => left.toString ctx ++ " = " ++ right.toString ctx
| .add left right => left.toString ctx ++ " + " ++ right.toString ctx
| .neg right => "-" ++ right.toString ctx
| .zero => "0"
| .app name input => name.toString ++ " " ++ input.toString ctx

#eval exact.toString

def next : StateM Nat Nat := do
  let x ← get
  modify (.+1)
  pure x

def Expr.interpretNormy (ctx : List Name := []) : Expr → StateM Nat String
| .bvar i => pure (Name.toString $ (ctx.get? i).map Name.toString)
| .forall name ty body => do
    let B ← body.interpretNormy (name :: ctx)
    pure ("⨆ " ++ name.toString ++ " ∈ " ++ ty.toString ++ ", " ++ B)
| .exists name ty body => do
    let B ← body.interpretNormy (name :: ctx)
    pure ("⨅ " ++ name.toString ++ " ∈ " ++ ty.toString ++ ", " ++ B)
| .implies left right => do
    let L ← left.interpretNormy ctx
    let n ← next
    let R ← right.interpretNormy ctx
    pure (R ++ " - k_" ++ toString n ++ " * " ++ L)
| .and left right => do
    let L ← left.interpretNormy ctx
    let n₁ ← next
    let n₂ ← next
    let R ← right.interpretNormy ctx
    pure ("k_" ++ toString n₁ ++ " * " ++ L ++ " + k_" ++ toString n₂ ++ " * " ++ R)
| .eq left right => do
    pure ("∥" ++ (← left.interpretNormy ctx) ++ " - " ++ (← right.interpretNormy ctx) ++ "∥")
| .add left right => do
    pure ((← left.interpretNormy ctx) ++ " + " ++ (← right.interpretNormy ctx))
| .neg right => do
    pure ("-" ++ (← right.interpretNormy ctx))
| .zero => (pure "0")
| .app name input => do
   pure (name.toString ++ " " ++ (← input.interpretNormy ctx))

#eval (exact.interpretNormy [] 0).1

end Liq
