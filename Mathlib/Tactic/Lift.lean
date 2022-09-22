/-
Copyright (c) 2019 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Johan Commelin
-/

import Std.Tactic.RCases
import Mathlib.Tactic.ShowTerm

/-!
# lift tactic

This file defines the `lift` tactic, allowing the user to lift elements from one type to another
under a specified condition.

## Tags

lift, tactic
-/

universe u v

/-- A class specifying that you can lift elements from `α` to `β` assuming `cond` is true.
  Used by the tactic `lift`. -/
class CanLift (α : Sort u) (β : Sort v) :=
(coe : β → α)
(cond : α → Prop)
(prf : ∀(x : α), cond x → ∃(y : β), coe y = x)

instance : CanLift Int Nat :=
⟨Coe.coe, fun n => 0 ≤ n, fun n hn =>
  match n with
  | .ofNat k => ⟨k, rfl⟩
  | .negSucc k => False.elim $ by cases hn⟩

/-- Enable automatic handling of pi types in `CanLift`. -/
instance pi.CanLift (ι : Sort _) (α β : ι → Sort _) [∀ i : ι, CanLift (α i) (β i)] :
  CanLift ((i : ι) → α i) ((i : ι) → β i) :=
{ coe := fun f i => CanLift.coe (f i),
  cond := fun f => ∀ i, CanLift.cond (β i) (f i),
  prf := fun f hf => ⟨fun i => Classical.choose (CanLift.prf (f i) (hf i)),
    funext fun i => Classical.choose_spec (CanLift.prf (f i) (hf i))⟩ }

theorem subtype.exists_pi_extension {ι : Sort _} {α : ι → Sort _} [ne : ∀ i, Nonempty (α i)]
  {p : ι → Prop} (f : (i : Subtype p) → α i) :
  ∃ g : ∀ i : ι, α i, (fun i : Subtype p => g i) = f :=
by
  open Classical in
  refine ⟨fun i => if hi : p i then f ⟨i, hi⟩ else choice (ne i), funext ?_⟩
  rintro ⟨i, hi⟩
  exact dif_pos hi

instance pi_subtype.CanLift (ι : Sort _) (α : ι → Sort _) [∀ i, Nonempty (α i)]
  (p : ι → Prop) :
  CanLift ((i : Subtype p) → α i) (∀ i, α i) :=
{ coe := fun f i => f i,
  cond := fun _ => true,
  prf := fun f _ => subtype.exists_pi_extension f }

instance pi_subtype.CanLift' (ι : Sort u) (α : Sort v) [Nonempty α] (p : ι → Prop) :
  _root_.CanLift (Subtype p → α) (ι → α) :=
pi_subtype.CanLift ι (fun _ => α) p

instance subtype.CanLift {α : Sort _} (p : α → Prop) : CanLift α {x // p x} :=
{ coe := Subtype.val, -- TODO: change this to `Coe.coe`
  cond := p,
  prf := fun a ha => ⟨⟨a, ha⟩, rfl⟩ }

open Lean Std.Tactic.RCases

def LiftCore (g : MVarId) (e new_ty h : Expr) (pat : RCasesPatt) :
  MetaM MVarId := do
  _
