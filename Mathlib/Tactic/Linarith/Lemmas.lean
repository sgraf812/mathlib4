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

theorem sub_eq_zero_of_eq [AddGroup G] {a b : G} : a = b → a - b = 0 := sorry

theorem sub_nonpos_of_le [AddGroup α] [LE α] [CovariantClass α α (swap (· + ·)) (· ≤ ·)] {a b : α} : a ≤ b → a - b ≤ 0 := sorry

theorem sub_neg_of_lt [AddGroup α] [LT α] [CovariantClass α α (swap (· + ·)) (· < ·)] {a b : α} : a < b → a - b < 0 := sorry

theorem neg_nonpos_of_nonneg [OrderedAddCommGroup α] {a : α} : 0 ≤ a → -a ≤ 0 := sorry

theorem neg_neg_of_pos [OrderedAddCommGroup α] {a : α} : 0 < a → -a < 0 := sorry