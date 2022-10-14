import Std.Tactic.Simpa
import Std.Tactic.Lint.Basic
import Mathlib.Algebra.Order.Ring

namespace Linarith

theorem mul_neg {α} [OrderedRing α] {a b : α} (ha : a < 0) (hb : 0 < b) : b * a < 0 :=
sorry
-- have : (-b)*a > 0 := mul_pos_of_neg_of_neg (neg_neg_of_pos hb) ha
-- neg_of_neg_pos (by simpa)

theorem mul_nonpos {α} [OrderedRing α] {a b : α} (ha : a ≤ 0) (hb : 0 < b) : b * a ≤ 0 :=
sorry
-- have : (-b)*a ≥ 0 := mul_nonneg_of_nonpos_of_nonpos (le_of_lt (neg_neg_of_pos hb)) ha
-- by simpa

-- used alongside `mul_neg` and `mul_nonpos`, so has the same argument pattern for uniformity
@[nolint unusedArguments]
theorem mul_eq {α} [OrderedSemiring α] {a b : α} (ha : a = 0) (_ : 0 < b) : b * a = 0 :=
sorry
-- by simp [*]

lemma eq_of_not_lt_of_not_gt {α} [LinearOrder α] (a b : α) (h1 : ¬ a < b) (h2 : ¬ b < a) : a = b :=
le_antisymm (le_of_not_gt h2) (le_of_not_gt h1)

end Linarith

section
open Function
-- These lemmas can be removed when their originals are ported.

theorem lt_zero_of_zero_gt [Zero α] [LT α] {a : α} (h : 0 > a) : a < 0 := h

theorem le_zero_of_zero_ge [Zero α] [LE α] {a : α} (h : 0 ≥ a) : a ≤ 0 := h

theorem sub_nonpos_of_le [AddGroup α] [LE α] [CovariantClass α α (swap (· + ·)) (· ≤ ·)] {a b : α} : a ≤ b → a - b ≤ 0 := sorry

theorem sub_neg_of_lt [AddGroup α] [LT α] [CovariantClass α α (swap (· + ·)) (· < ·)] {a b : α} : a < b → a - b < 0 := sorry

theorem neg_nonpos_of_nonneg [OrderedAddCommGroup α] {a : α} : 0 ≤ a → -a ≤ 0 := sorry

theorem neg_neg_of_pos [OrderedAddCommGroup α] {a : α} : 0 < a → -a < 0 := sorry



-- These can be deleted. They are just "tests" that we're finding expected instances

example {α} [LinearOrderedAddCommGroup α] : OrderedAddCommGroup α :=
  inferInstance
  -- LinearOrderedAddCommGroup.toOrderedAddCommGroup

example {α} [OrderedAddCommGroup α] : AddCommGroup α :=
  inferInstance
  -- OrderedAddCommGroup.toAddCommGroup

example {α} [AddCommGroup α] : AddGroup α :=
  inferInstance
  -- AddCommGroup.toAddGroup

example {α} [AddGroup α] : AddCancelMonoid α :=
  inferInstance
  -- AddGroup.toAddCancelMonoid

example {α} [AddCancelMonoid α] : AddRightCancelMonoid α :=
  inferInstance
  -- AddCancelMonoid.toAddRightCancelMonoid

example {α} [AddRightCancelMonoid α] : AddRightCancelSemigroup α :=
  inferInstance
  -- AddRightCancelMonoid.toAddRightCancelSemigroup

example {α} [OrderedAddCommGroup α] : OrderedCancelAddCommMonoid α :=
  inferInstance
  -- OrderedAddCommGroup.toOrderedCancelAddCommMonoid

example {α} [OrderedCancelAddCommMonoid α] : OrderedAddCommMonoid α :=
  inferInstance
  -- OrderedCancelAddCommMonoid.toOrderedAddCommMonoid

example {α} [LinearOrderedAddCommGroup α] : OrderedAddCommMonoid α :=
  inferInstance
  -- OrderedCancelAddCommMonoid.toOrderedAddCommMonoid

example {α} [OrderedAddCommMonoid α] : CovariantClass α α (swap (· + ·)) (· ≤ ·) :=
  -- inferInstance
  OrderedAddCommMonoid.to_covariant_class_right α

example {α} [LinearOrderedAddCommGroup α] : CovariantClass α α (swap (· + ·)) (· ≤ ·) :=
  OrderedAddCommMonoid.to_covariant_class_right α

example {α} [OrderedAddCommGroup α] : PartialOrder α :=
  OrderedAddCommGroup.toPartialOrder

example {α} [AddRightCancelSemigroup α] [PartialOrder α] [CovariantClass α α (swap (· + ·)) (· ≤ ·)] :
    CovariantClass α α (swap (· + ·)) (· < ·) :=
  AddRightCancelSemigroup.covariant_swap_add_lt_of_covariant_swap_add_le α

example {α} [LinearOrderedAddCommGroup α] :
    CovariantClass α α (swap (· + ·)) (· < ·) :=
  AddRightCancelSemigroup.covariant_swap_add_lt_of_covariant_swap_add_le α
