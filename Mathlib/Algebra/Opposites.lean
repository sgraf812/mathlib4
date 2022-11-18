/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Algebra.Group.Defs
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Nontrivial
import Mathlib.Logic.IsEmpty

/-!

# Multiplicative opposite and algebraic operations on it

In this file we define `mul_opposite α = αᵐᵒᵖ` to be the multiplicative opposite of `α`. It inherits
all additive algebraic structures on `α` (in other files), and reverses the order of multipliers in
multiplicative structures, i.e., `op (x * y) = op y * op x`, where `mul_opposite.op` is the
canonical map from `α` to `αᵐᵒᵖ`.

We also define `add_opposite α = αᵃᵒᵖ` to be the additive opposite of `α`. It inherits all
multiplicative algebraic structures on `α` (in other files), and reverses the order of summands in
additive structures, i.e. `op (x + y) = op y + op x`, where `add_opposite.op` is the canonical map
from `α` to `αᵃᵒᵖ`.

## Notation

* `αᵐᵒᵖ = mul_opposite α`
* `αᵃᵒᵖ = add_opposite α`

## Tags

multiplicative opposite, additive opposite
-/


universe u v

open Function

/-- Multiplicative opposite of a type. This type inherits all additive structures on `α` and
reverses left and right in multiplication.-/
@[to_additive
      "Additive opposite of a type. This type inherits all multiplicative structures on\n
      `α` and reverses left and right in addition."]
def MulOpposite (α : Type u) : Type u :=
  α
#align mul_opposite MulOpposite

-- mathport name: «expr ᵐᵒᵖ»
postfix:max "ᵐᵒᵖ" => MulOpposite

-- mathport name: «expr ᵃᵒᵖ»
postfix:max "ᵃᵒᵖ" => AddOpposite

variable {α : Type u}

namespace MulOpposite

/-- The element of `mul_opposite α` that represents `x : α`. -/
--@[pp_nodot,
@[to_additive "The element of `αᵃᵒᵖ` that represents `x : α`."]
def op : α → αᵐᵒᵖ :=
  id
#align mul_opposite.op MulOpposite.op

/-- The element of `α` represented by `x : αᵐᵒᵖ`. -/
--@[pp_nodot,
@[to_additive "The element of `α` represented by `x : αᵃᵒᵖ`."]
def unop : αᵐᵒᵖ → α :=
  id
#align mul_opposite.unop MulOpposite.unop

--attribute [pp_nodot] AddOpposite.op AddOpposite.unop

@[simp, to_additive]
theorem unop_op (x : α) : unop (op x) = x :=
  rfl
#align mul_opposite.unop_op MulOpposite.unop_op

@[simp, to_additive]
theorem op_unop (x : αᵐᵒᵖ) : op (unop x) = x :=
  rfl
#align mul_opposite.op_unop MulOpposite.op_unop

@[simp, to_additive]
theorem op_comp_unop : (op : α → αᵐᵒᵖ) ∘ unop = id :=
  rfl
#align mul_opposite.op_comp_unop MulOpposite.op_comp_unop

@[simp, to_additive]
theorem unop_comp_op : (unop : αᵐᵒᵖ → α) ∘ op = id :=
  rfl
#align mul_opposite.unop_comp_op MulOpposite.unop_comp_op

/-- A recursor for `mul_opposite`. Use as `induction x using mul_opposite.rec`. -/
@[simp, to_additive "A recursor for `add_opposite`. Use as `induction x using add_opposite.rec`."]
protected def rec {F : ∀ _ : αᵐᵒᵖ, Sort v} (h : ∀ X, F (op X)) : ∀ X, F X := fun X => h (unop X)
#align mul_opposite.rec MulOpposite.rec

/-- The canonical bijection between `α` and `αᵐᵒᵖ`. -/
@[to_additive "The canonical bijection between `α` and `αᵃᵒᵖ`.",--]
  simps (config := { fullyApplied := false }) apply]
def opEquiv : α ≃ αᵐᵒᵖ :=
  ⟨op, unop, unop_op, op_unop⟩
#align mul_opposite.op_equiv MulOpposite.opEquiv

-- porting note: We have to provide this lemma by hand, since the autogenerated version makes the
-- simpNF linter unhappy
lemma opEquiv_symm_apply : (opEquiv.symm.toFun : αᵐᵒᵖ → α) = unop := rfl

@[to_additive]
theorem op_bijective : Bijective (op : α → αᵐᵒᵖ) :=
  opEquiv.bijective
#align mul_opposite.op_bijective MulOpposite.op_bijective

@[to_additive]
theorem unop_bijective : Bijective (unop : αᵐᵒᵖ → α) :=
  opEquiv.symm.bijective
#align mul_opposite.unop_bijective MulOpposite.unop_bijective

@[to_additive]
theorem op_injective : Injective (op : α → αᵐᵒᵖ) :=
  op_bijective.injective
#align mul_opposite.op_injective MulOpposite.op_injective

@[to_additive]
theorem op_surjective : Surjective (op : α → αᵐᵒᵖ) :=
  op_bijective.surjective
#align mul_opposite.op_surjective MulOpposite.op_surjective

@[to_additive]
theorem unop_injective : Injective (unop : αᵐᵒᵖ → α) :=
  unop_bijective.injective
#align mul_opposite.unop_injective MulOpposite.unop_injective

@[to_additive]
theorem unop_surjective : Surjective (unop : αᵐᵒᵖ → α) :=
  unop_bijective.surjective
#align mul_opposite.unop_surjective MulOpposite.unop_surjective

@[simp, to_additive]
theorem op_inj {x y : α} : op x = op y ↔ x = y :=
  op_injective.eq_iff
#align mul_opposite.op_inj MulOpposite.op_inj

@[simp, to_additive]
theorem unop_inj {x y : αᵐᵒᵖ} : unop x = unop y ↔ x = y :=
  unop_injective.eq_iff
#align mul_opposite.unop_inj MulOpposite.unop_inj

variable (α)

@[to_additive]
instance [Nontrivial α] : Nontrivial αᵐᵒᵖ :=
  op_injective.nontrivial

@[to_additive]
instance [Inhabited α] : Inhabited αᵐᵒᵖ :=
  ⟨op default⟩

@[to_additive]
instance [Subsingleton α] : Subsingleton αᵐᵒᵖ :=
  unop_injective.subsingleton

@[to_additive]
instance [Unique α] : Unique αᵐᵒᵖ :=
  Unique.mk' _

@[to_additive]
instance [IsEmpty α] : IsEmpty αᵐᵒᵖ :=
  Function.isEmpty unop

instance [Zero α] : Zero αᵐᵒᵖ where zero := op 0

@[to_additive]
instance [One α] : One αᵐᵒᵖ where one := op 1

instance [Add α] : Add αᵐᵒᵖ where add x y := op (unop x + unop y)

instance [Sub α] : Sub αᵐᵒᵖ where sub x y := op (unop x - unop y)

instance [Neg α] : Neg αᵐᵒᵖ where neg x := op $ -unop x

instance [HasInvolutiveNeg α] : HasInvolutiveNeg αᵐᵒᵖ :=
  { MulOpposite.instNegMulOpposite α with neg_neg := fun _ => unop_injective $ neg_neg _ }

@[to_additive]
instance [Mul α] : Mul αᵐᵒᵖ where mul x y := op (unop y * unop x)

@[to_additive]
instance [Inv α] : Inv αᵐᵒᵖ where inv x := op $ (unop x)⁻¹

@[to_additive]
instance [HasInvolutiveInv α] : HasInvolutiveInv αᵐᵒᵖ :=
  { MulOpposite.instInvMulOpposite α with inv_inv := fun _ => unop_injective $ inv_inv _ }

@[to_additive]
instance (R : Type _) [HasSmul R α] : HasSmul R αᵐᵒᵖ where smul c x := op (c • unop x)

section

--variable (α)

@[simp]
theorem op_zero [Zero α] : op (0 : α) = 0 :=
  rfl
#align mul_opposite.op_zero MulOpposite.op_zero

@[simp]
theorem unop_zero [Zero α] : unop (0 : αᵐᵒᵖ) = 0 :=
  rfl
#align mul_opposite.unop_zero MulOpposite.unop_zero

@[simp, to_additive]
theorem op_one [One α] : op (1 : α) = 1 :=
  rfl
#align mul_opposite.op_one MulOpposite.op_one

@[simp, to_additive]
theorem unop_one [One α] : unop (1 : αᵐᵒᵖ) = 1 :=
  rfl
#align mul_opposite.unop_one MulOpposite.unop_one

variable {α}

@[simp]
theorem op_add [Add α] (x y : α) : op (x + y) = op x + op y :=
  rfl
#align mul_opposite.op_add MulOpposite.op_add

@[simp]
theorem unop_add [Add α] (x y : αᵐᵒᵖ) : unop (x + y) = unop x + unop y :=
  rfl
#align mul_opposite.unop_add MulOpposite.unop_add

@[simp]
theorem op_neg [Neg α] (x : α) : op (-x) = -op x :=
  rfl
#align mul_opposite.op_neg MulOpposite.op_neg

@[simp]
theorem unop_neg [Neg α] (x : αᵐᵒᵖ) : unop (-x) = -unop x :=
  rfl
#align mul_opposite.unop_neg MulOpposite.unop_neg

@[simp, to_additive]
theorem op_mul [Mul α] (x y : α) : op (x * y) = op y * op x :=
  rfl
#align mul_opposite.op_mul MulOpposite.op_mul

@[simp, to_additive]
theorem unop_mul [Mul α] (x y : αᵐᵒᵖ) : unop (x * y) = unop y * unop x :=
  rfl
#align mul_opposite.unop_mul MulOpposite.unop_mul

@[simp, to_additive]
theorem op_inv [Inv α] (x : α) : op x⁻¹ = (op x)⁻¹ :=
  rfl
#align mul_opposite.op_inv MulOpposite.op_inv

@[simp, to_additive]
theorem unop_inv [Inv α] (x : αᵐᵒᵖ) : unop x⁻¹ = (unop x)⁻¹ :=
  rfl
#align mul_opposite.unop_inv MulOpposite.unop_inv

@[simp]
theorem op_sub [Sub α] (x y : α) : op (x - y) = op x - op y :=
  rfl
#align mul_opposite.op_sub MulOpposite.op_sub

@[simp]
theorem unop_sub [Sub α] (x y : αᵐᵒᵖ) : unop (x - y) = unop x - unop y :=
  rfl
#align mul_opposite.unop_sub MulOpposite.unop_sub

@[simp, to_additive]
theorem op_smul {R : Type _} [HasSmul R α] (c : R) (a : α) : op (c • a) = c • op a :=
  rfl
#align mul_opposite.op_smul MulOpposite.op_smul

@[simp, to_additive]
theorem unop_smul {R : Type _} [HasSmul R α] (c : R) (a : αᵐᵒᵖ) : unop (c • a) = c • unop a :=
  rfl
#align mul_opposite.unop_smul MulOpposite.unop_smul

end

variable {α}

@[simp]
theorem unop_eq_zero_iff [Zero α] (a : αᵐᵒᵖ) : a.unop = (0 : α) ↔ a = (0 : αᵐᵒᵖ) :=
  unop_injective.eq_iff' rfl
#align mul_opposite.unop_eq_zero_iff MulOpposite.unop_eq_zero_iff

@[simp]
theorem op_eq_zero_iff [Zero α] (a : α) : op a = (0 : αᵐᵒᵖ) ↔ a = (0 : α) :=
  op_injective.eq_iff' rfl
#align mul_opposite.op_eq_zero_iff MulOpposite.op_eq_zero_iff

theorem unop_ne_zero_iff [Zero α] (a : αᵐᵒᵖ) : a.unop ≠ (0 : α) ↔ a ≠ (0 : αᵐᵒᵖ) :=
  not_congr $ unop_eq_zero_iff a
#align mul_opposite.unop_ne_zero_iff MulOpposite.unop_ne_zero_iff

theorem op_ne_zero_iff [Zero α] (a : α) : op a ≠ (0 : αᵐᵒᵖ) ↔ a ≠ (0 : α) :=
  not_congr $ op_eq_zero_iff a
#align mul_opposite.op_ne_zero_iff MulOpposite.op_ne_zero_iff

@[simp, to_additive]
theorem unop_eq_one_iff [One α] (a : αᵐᵒᵖ) : a.unop = 1 ↔ a = 1 :=
  unop_injective.eq_iff' rfl
#align mul_opposite.unop_eq_one_iff MulOpposite.unop_eq_one_iff

@[simp, to_additive]
theorem op_eq_one_iff [One α] (a : α) : op a = 1 ↔ a = 1 :=
  op_injective.eq_iff' rfl
#align mul_opposite.op_eq_one_iff MulOpposite.op_eq_one_iff

end MulOpposite

namespace AddOpposite

instance [One α] : One αᵃᵒᵖ where one := op 1

@[simp]
theorem op_one [One α] : op (1 : α) = 1 :=
  rfl
#align add_opposite.op_one AddOpposite.op_one

@[simp]
theorem unop_one [One α] : unop 1 = (1 : α) :=
  rfl
#align add_opposite.unop_one AddOpposite.unop_one

@[simp]
theorem op_eq_one_iff [One α] {a : α} : op a = 1 ↔ a = 1 :=
  op_injective.eq_iff' op_one
#align add_opposite.op_eq_one_iff AddOpposite.op_eq_one_iff

@[simp]
theorem unop_eq_one_iff [One α] {a : αᵃᵒᵖ} : unop a = 1 ↔ a = 1 :=
  unop_injective.eq_iff' unop_one
#align add_opposite.unop_eq_one_iff AddOpposite.unop_eq_one_iff

instance [Mul α] : Mul αᵃᵒᵖ where mul a b := op (unop a * unop b)

@[simp]
theorem op_mul [Mul α] (a b : α) : op (a * b) = op a * op b :=
  rfl
#align add_opposite.op_mul AddOpposite.op_mul

@[simp]
theorem unop_mul [Mul α] (a b : αᵃᵒᵖ) : unop (a * b) = unop a * unop b :=
  rfl
#align add_opposite.unop_mul AddOpposite.unop_mul

instance [Inv α] : Inv αᵃᵒᵖ where inv a := op (unop a)⁻¹

instance [HasInvolutiveInv α] : HasInvolutiveInv αᵃᵒᵖ :=
  { AddOpposite.instInvAddOpposite with inv_inv := fun _ => unop_injective $ inv_inv _ }

@[simp]
theorem op_inv [Inv α] (a : α) : op a⁻¹ = (op a)⁻¹ :=
  rfl
#align add_opposite.op_inv AddOpposite.op_inv

@[simp]
theorem unop_inv [Inv α] (a : αᵃᵒᵖ) : unop a⁻¹ = (unop a)⁻¹ :=
  rfl
#align add_opposite.unop_inv AddOpposite.unop_inv

instance [Div α] : Div αᵃᵒᵖ where div a b := op (unop a / unop b)

@[simp]
theorem op_div [Div α] (a b : α) : op (a / b) = op a / op b :=
  rfl
#align add_opposite.op_div AddOpposite.op_div

@[simp]
theorem unop_div [Div α] (a b : α) : unop (a / b) = unop a / unop b :=
  rfl
#align add_opposite.unop_div AddOpposite.unop_div

end AddOpposite
