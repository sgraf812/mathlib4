/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Tactic.Basic
import Mathlib.Init.Function
import Mathlib.Logic.Function.Basic

/-!
# Extra facts about `prod`

This file defines `prod.swap : α × β → β × α` and proves various simple lemmas about `prod`.

Porting notes:

There is already a lemma `Prod.ext` in core which is not exactly what we want so the
ported `prod.ext` is now called `Prod.ext'`.
-/


variable {α : Type _} {β : Type _} {γ : Type _} {δ : Type _}

@[simp]
theorem prod_map (f : α → γ) (g : β → δ) (p : α × β) : Prod.map f g p = (f p.1, g p.2) :=
  rfl

namespace Prod

@[simp]
theorem «forall» {p : α × β → Prop} : (∀ x, p x) ↔ ∀ a b, p (a, b) :=
  ⟨fun h a b => h (a, b), fun h ⟨a, b⟩ => h a b⟩

@[simp]
theorem «exists» {p : α × β → Prop} : (∃ x, p x) ↔ ∃ a b, p (a, b) :=
  ⟨fun ⟨⟨a, b⟩, h⟩ => ⟨a, b, h⟩, fun ⟨a, b, h⟩ => ⟨⟨a, b⟩, h⟩⟩

theorem forall' {p : α → β → Prop} : (∀ x : α × β, p x.1 x.2) ↔ ∀ a b, p a b :=
  Prod.forall

theorem exists' {p : α → β → Prop} : (∃ x : α × β, p x.1 x.2) ↔ ∃ a b, p a b :=
  Prod.exists

@[simp]
theorem snd_comp_mk (x : α) : Prod.snd ∘ (Prod.mk x : β → α × β) = id :=
  rfl

@[simp]
theorem fst_comp_mk (x : α) : Prod.fst ∘ (Prod.mk x : β → α × β) = Function.const β x :=
  rfl

@[simp]
theorem map_mk (f : α → γ) (g : β → δ) (a : α) (b : β) : map f g (a, b) = (f a, g b) :=
  rfl

theorem map_fst (f : α → γ) (g : β → δ) (p : α × β) : (map f g p).1 = f p.1 :=
  rfl

theorem map_snd (f : α → γ) (g : β → δ) (p : α × β) : (map f g p).2 = g p.2 :=
  rfl

theorem map_fst' (f : α → γ) (g : β → δ) : Prod.fst ∘ map f g = f ∘ Prod.fst :=
  funext <| map_fst f g

theorem map_snd' (f : α → γ) (g : β → δ) : Prod.snd ∘ map f g = g ∘ Prod.snd :=
  funext <| map_snd f g

/-- Composing a `prod.map` with another `prod.map` is equal to
a single `prod.map` of composed functions.
-/
theorem map_comp_map {ε ζ : Type _} (f : α → β) (f' : γ → δ) (g : β → ε) (g' : δ → ζ) :
    Prod.map g g' ∘ Prod.map f f' = Prod.map (g ∘ f) (g' ∘ f') :=
  rfl

/-- Composing a `prod.map` with another `prod.map` is equal to
a single `prod.map` of composed functions, fully applied.
-/
theorem map_map {ε ζ : Type _} (f : α → β) (f' : γ → δ) (g : β → ε) (g' : δ → ζ) (x : α × γ) :
    Prod.map g g' (Prod.map f f' x) = Prod.map (g ∘ f) (g' ∘ f') x :=
  rfl

@[simp]
theorem mk.inj_iff {a₁ a₂ : α} {b₁ b₂ : β} : (a₁, b₁) = (a₂, b₂) ↔ a₁ = a₂ ∧ b₁ = b₂ :=
  ⟨Prod.mk.inj, by intro ⟨ha, hb⟩; rw [ha, hb]⟩

theorem mk.inj_left {α β : Type _} (a : α) : Function.injective (Prod.mk a : β → α × β) := by
  intro b₁ b₂ h
  simpa only [true_and, Prod.mk.inj_iff, eq_self_iff_true] using h

theorem mk.inj_right {α β : Type _} (b : β) : Function.injective (fun a => Prod.mk a b : α → α × β) := by
  intro b₁ b₂ h
  · simpa only [and_true, eq_self_iff_true, mk.inj_iff] using h


theorem ext_iff {p q : α × β} : p = q ↔ p.1 = q.1 ∧ p.2 = q.2 := by
  cases p
  cases q
  rw [mk.inj_iff]

@[ext]
theorem ext' {α β} {p q : α × β} (h₁ : p.1 = q.1) (h₂ : p.2 = q.2) : p = q :=
  ext_iff.2 ⟨h₁, h₂⟩

theorem map_def {f : α → γ} {g : β → δ} : Prod.map f g = fun p : α × β => (f p.1, g p.2) :=
  funext fun p => ext' (map_fst f g p) (map_snd f g p)

theorem id_prod : (fun p : α × β => (p.1, p.2)) = id :=
  funext fun ⟨_, _⟩ => rfl

theorem map_id : Prod.map (@id α) (@id β) = id :=
  id_prod

theorem fst_surjective [h : Nonempty β] : Function.surjective (@fst α β) := fun x => h.elim fun y => ⟨⟨x, y⟩, rfl⟩

theorem snd_surjective [h : Nonempty α] : Function.surjective (@snd α β) := fun y => h.elim fun x => ⟨⟨x, y⟩, rfl⟩

theorem fst_injective [Subsingleton β] : Function.injective (@fst α β) := fun _ _ h => ext' h (Subsingleton.elim _ _)

theorem snd_injective [Subsingleton α] : Function.injective (@snd α β) := fun _ _ h => ext' (Subsingleton.elim _ _) h

/-- Swap the factors of a product. `swap (a, b) = (b, a)` -/
def swap : α × β → β × α := fun p => (p.2, p.1)

@[simp]
theorem swap_swap : ∀ x : α × β, swap (swap x) = x
  | ⟨_, _⟩ => rfl

@[simp]
theorem fst_swap {p : α × β} : (swap p).1 = p.2 :=
  rfl

@[simp]
theorem snd_swap {p : α × β} : (swap p).2 = p.1 :=
  rfl

@[simp]
theorem swap_prod_mk {a : α} {b : β} : swap (a, b) = (b, a) :=
  rfl

@[simp]
theorem swap_swap_eq : swap ∘ swap = @id (α × β) :=
  funext swap_swap

@[simp]
theorem swap_left_inverse : Function.LeftInverse (@swap α β) swap :=
  swap_swap

@[simp]
theorem swap_right_inverse : Function.RightInverse (@swap α β) swap :=
  swap_swap

theorem swap_injective : Function.injective (@swap α β) :=
  swap_left_inverse.injective

theorem swap_surjective : Function.surjective (@swap α β) :=
  swap_left_inverse.surjective

theorem swap_bijective : Function.bijective (@swap α β) :=
  ⟨swap_injective, swap_surjective⟩

@[simp]
theorem swap_inj {p q : α × β} : swap p = swap q ↔ p = q :=
  swap_injective.eq_iff

theorem eq_iff_fst_eq_snd_eq : ∀ {p q : α × β}, p = q ↔ p.1 = q.1 ∧ p.2 = q.2
  | ⟨p₁, p₂⟩, ⟨q₁, q₂⟩ => by simp

theorem fst_eq_iff : ∀ {p : α × β} {x : α}, p.1 = x ↔ p = (x, p.2)
  | ⟨a, b⟩, x => by simp

theorem snd_eq_iff : ∀ {p : α × β} {x : β}, p.2 = x ↔ p = (p.1, x)
  | ⟨a, b⟩, x => by simp

theorem lex_def (r : α → α → Prop) (s : β → β → Prop) {p q : α × β} :
    Prod.Lex r s p q ↔ r p.1 q.1 ∨ p.1 = q.1 ∧ s p.2 q.2 :=
  ⟨fun h => by cases h <;> simp [*], fun h =>
    match p, q, h with
    | (a, b), (c, d), Or.inl h => Lex.left _ _ h
    | (a, b), (c, d), Or.inr ⟨e, h⟩ => by
      change a = c at e
      subst e <;> exact lex.right _ h⟩

instance Lex.decidable [DecidableEq α] (r : α → α → Prop) (s : β → β → Prop) [DecidableRel r] [DecidableRel s] :
    DecidableRel (Prod.Lex r s) := fun _ _ => decidable_of_decidable_of_iff (lex_def r s).symm
set_option autoImplicit false
--@[refl]
theorem Lex.refl_left (r : α → α → Prop) (s : β → β → Prop) [IsRefl α r] : ∀ x, Prod.Lex r s x x
  | (x₁, x₂) => Lex.left _ _ (refl _)

instance is_refl_left {r : α → α → Prop} {s : β → β → Prop} [IsRefl α r] : IsRefl (α × β) (Lex r s) :=
  ⟨Lex.refl_left _ _⟩

--@[refl]
theorem Lex.refl_right (r : α → α → Prop) (s : β → β → Prop) [IsRefl β s] : ∀ x, Prod.Lex r s x x
  | (x₁, x₂) => Lex.right _ (refl _)

instance is_refl_right {r : α → α → Prop} {s : β → β → Prop} [IsRefl β s] : IsRefl (α × β) (Lex r s) :=
  ⟨Lex.refl_right _ _⟩

@[trans]
theorem Lex.trans {r : α → α → Prop} {s : β → β → Prop} [IsTrans α r] [IsTrans β s] :
    ∀ {x y z : α × β}, Prod.Lex r s x y → Prod.Lex r s y z → Prod.Lex r s x z
  | (x₁, x₂), (y₁, y₂), (z₁, z₂), lex.left _ _ hxy₁, lex.left _ _ hyz₁ => Lex.left _ _ (trans hxy₁ hyz₁)
  | (x₁, x₂), (y₁, y₂), (z₁, z₂), lex.left _ _ hxy₁, lex.right _ hyz₂ => Lex.left _ _ hxy₁
  | (x₁, x₂), (y₁, y₂), (z₁, z₂), lex.right _ _, lex.left _ _ hyz₁ => Lex.left _ _ hyz₁
  | (x₁, x₂), (y₁, y₂), (z₁, z₂), lex.right _ hxy₂, lex.right _ hyz₂ => Lex.right _ (trans hxy₂ hyz₂)

instance {r : α → α → Prop} {s : β → β → Prop} [IsTrans α r] [IsTrans β s] : IsTrans (α × β) (Lex r s) :=
  ⟨fun _ _ _ => Lex.trans⟩

instance {r : α → α → Prop} {s : β → β → Prop} [IsStrictOrder α r] [IsAntisymm β s] : IsAntisymm (α × β) (Lex r s) :=
  ⟨fun x₁ x₂ h₁₂ h₂₁ =>
    match x₁, x₂, h₁₂, h₂₁ with
    | (a₁, b₁), (a₂, b₂), lex.left _ _ hr₁, lex.left _ _ hr₂ => (irrefl a₁ (trans hr₁ hr₂)).elim
    | (a₁, b₁), (a₂, b₂), lex.left _ _ hr₁, lex.right _ _ => (irrefl _ hr₁).elim
    | (a₁, b₁), (a₂, b₂), lex.right _ _, lex.left _ _ hr₂ => (irrefl _ hr₂).elim
    | (a₁, b₁), (a₂, b₂), lex.right _ hs₁, lex.right _ hs₂ => antisymm hs₁ hs₂ ▸ rfl⟩

instance is_total_left {r : α → α → Prop} {s : β → β → Prop} [IsTotal α r] : IsTotal (α × β) (Lex r s) :=
  ⟨fun ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ => (IsTotal.total a₁ a₂).imp (Lex.left _ _) (Lex.left _ _)⟩

instance is_total_right {r : α → α → Prop} {s : β → β → Prop} [IsTrichotomous α r] [IsTotal β s] :
    IsTotal (α × β) (Lex r s) :=
  ⟨fun ⟨i, a⟩ ⟨j, b⟩ => by
    obtain hij | rfl | hji := trichotomous_of r i j
    · exact Or.inl (lex.left _ _ hij)

    · exact (total_of s a b).imp (lex.right _) (lex.right _)

    · exact Or.inr (lex.left _ _ hji)
      ⟩

end Prod

open Prod

namespace Function

variable {f : α → γ} {g : β → δ} {f₁ : α → β} {g₁ : γ → δ} {f₂ : β → α} {g₂ : δ → γ}

theorem injective.prod_map (hf : injective f) (hg : injective g) : injective (map f g) :=
  fun _ _ h => ext' (hf (ext_iff.1 h).1) (hg <| (ext_iff.1 h).2)

theorem surjective.prod_map (hf : surjective f) (hg : surjective g) : surjective (map f g) := fun p =>
  let ⟨x, hx⟩ := hf p.1
  let ⟨y, hy⟩ := hg p.2
  ⟨(x, y), Prod.ext' hx hy⟩

theorem Bijective.prod_map (hf : bijective f) (hg : bijective g) : bijective (map f g) :=
  ⟨hf.1.prod_map hg.1, hf.2.prod_map hg.2⟩

theorem LeftInverse.prod_map (hf : LeftInverse f₁ f₂) (hg : LeftInverse g₁ g₂) :
    LeftInverse (map f₁ g₁) (map f₂ g₂) :=
  fun a => by rw [Prod.map_map, hf.comp_eq_id, hg.comp_eq_id, map_id, id]

theorem RightInverse.prod_map :
    RightInverse f₁ f₂ → RightInverse g₁ g₂ → RightInverse (map f₁ g₁) (map f₂ g₂) :=
  LeftInverse.prod_map

theorem Involutive.prod_map {f : α → α} {g : β → β} :
    involutive f → involutive g → involutive (map f g) :=
  LeftInverse.prod_map

end Function
