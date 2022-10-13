import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Order.MonoidLemmas

open Function

/-- An ordered additive commutative group is an additive commutative group
with a partial order in which addition is strictly monotone. -/
class OrderedAddCommGroup (α : Type u) extends AddCommGroup α, PartialOrder α where
  add_le_add_left : ∀ a b : α, a ≤ b → ∀ c : α, c + a ≤ c + b

section Group
variable [Group α] [LT α]

section TypeclassesLeftLt

variable [CovariantClass α α (· * ·) (· < ·)] {a b c : α}

/-- Uses `Left` co(ntra)variant. -/
@[simp, to_additive Left.neg_pos_iff "Uses `Left` co(ntra)variant."]
theorem Left.one_lt_inv_iff : 1 < a⁻¹ ↔ a < 1 := by
  rw [← mul_lt_mul_iff_left a, mul_inv_self, mul_one]

end TypeclassesLeftLt

section Right

variable [CovariantClass α α (swap (· * ·)) (· < ·)] {a b c d : α}

-- FIXME: restore @[to_additive sub_pos]
@[simp]
theorem one_lt_div' : 1 < a / b ↔ b < a := by
  rw [← mul_lt_mul_iff_right b, one_mul, div_eq_mul_inv, inv_mul_cancel_right]

end Right

end Group

alias Left.one_lt_inv_iff ↔ _ one_lt_inv_of_inv
attribute [to_additive neg_pos_of_neg] one_lt_inv_of_inv

/-!
### Linearly ordered commutative groups
-/


/-- A linearly ordered additive commutative group is an
additive commutative group with a linear order in which
addition is monotone. -/
class LinearOrderedAddCommGroup (α : Type u) extends OrderedAddCommGroup α, LinearOrder α
