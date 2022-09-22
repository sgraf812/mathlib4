-- import data.int.basic
import Mathlib.Tactic.Lift

/-! Some tests of the `lift` tactic. -/

example (n m k x z u : Int) (hn : 0 < n) (hk : 0 ≤ k + n) (hu : 0 ≤ u)
  (h : k + n = 2 + x) (f : false) :
  k + n = m + x :=
by
  lift n to Nat using le_of_lt hn
    guard_target (k + ↑n = m + x), guard_hyp hn : (0 : Int) < ↑n
  lift m to Nat
    guard_target (k + ↑n = ↑m + x), tactic.swap, guard_target (0 ≤ m), tactic.swap
    tactic.num_goals >>= λ n, guard (n = 2)
  lift (k + n) to Nat using hk with l hl
    guard_hyp l : Nat, guard_hyp hl : ↑l = k + ↑n, guard_target (↑l = ↑m + x)
    tactic.success_if_fail (tactic.get_local `hk)
  lift x to Nat with y hy
    guard_hyp y : Nat, guard_hyp hy : ↑y = x, guard_target (↑l = ↑m + x)
  lift z to Nat with w
    guard_hyp w : Nat, tactic.success_if_fail (tactic.get_local `z)
  lift u to Nat using hu with u rfl hu
    guard_hyp hu : (0 : Int) ≤ ↑u

  all_goals { exfalso, assumption }

-- test lift of functions
example (α : Type _) (f : α → Int) (hf : ∀ a, 0 ≤ f a) (hf' : ∀ a, f a < 1) (a : α) :
  0 ≤ 2 * f a :=
by
  lift f to α → Nat using hf
    guard_target ((0:Int) ≤ 2 * (λ i : α, (f i : Int)) a)
    guard_hyp hf' : ∀ a, ((λ i : α, (f i:Int)) a) < 1
  exact int.coe_nat_nonneg _

-- fail gracefully when the lifted variable is a local definition
example : let n : Int := 3; n = n :=
by
  intro n
  success_if_fail_with_msg { lift n to Nat }
    ("Cannot substitute variable n, it is a local definition. " ++
    "If you really want to do this, use `clear_value` first.")
  refl

instance CanLift_unit : CanLift unit unit :=
⟨id, fun _ => true, fun x _ => ⟨x, rfl⟩⟩

/- test whether new instances of `CanLift` are added as simp lemmas -/
run_cmd do l ← CanLift_attr.get_cache, guard (`CanLift_unit ∈ l)

/- test error messages -/
example (n : Int) (hn : 0 < n) : true :=
by
  success_if_fail_with_msg {lift n to Nat using hn} "lift tactic failed.
invalid type ascription, term has type\n  0 < n\nbut is expected to have type\n  0 ≤ n"
  success_if_fail_with_msg {lift (n : option Int) to Nat}
    "Failed to find a lift from option Int to Nat. Provide an instance of\n  CanLift (option Int) Nat"
  trivial

example (n : Int) : Nat :=
by
  success_if_fail_with_msg {lift n to Nat}
    "lift tactic failed. Tactic is only applicable when the target is a proposition."
  exact 0

instance CanLift_set (R : Type _) (s : set R) : CanLift R s :=
{ coe := coe,
  cond := (. ∈ s),
  prf := fun x hx => ⟨⟨x, hx⟩, rfl⟩ }

example {R : Type _} {P : R → Prop} (x : R) (hx : P x) : true :=
by lift x to {x // P x} using hx with y; trivial

/-! Test that `lift` elaborates `s` as a type, not as a set. -/
example {R : Type _} {s : set R} (x : R) (hx : x ∈ s) : true :=
by lift x to s using hx with y; trivial

example (n : Int) (hn : 0 ≤ n) : true :=
by lift n to Nat; trivial; exact hn

example (n : Int) (hn : 0 ≤ n) : true :=
by lift n to Nat using hn; trivial

example (n : Int) (hn : n ≥ 0) : true :=
by
  lift n to Nat using ge.le _
  trivial
  guard_target (n ≥ 0)
  exact hn

example (n : Int) (hn : 0 ≤ 1 * n) : true :=
by
  lift n to Nat using by { simpa [int.one_mul] using hn } with k
  -- the above braces are optional, but it would be bad style to remove them (see next example)
  guard_hyp hn : 0 ≤ 1 * ((k : Nat) : Int)
  trivial

example (n : Int) (hn : 0 ≤ n ↔ true) : true :=
by
  lift n to Nat using by { simp [hn] } with k -- the braces are not optional here
  trivial
