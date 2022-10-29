/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Floris van Doorn
-/
import Std.Tactic.Ext
import Std.Tactic.Lint.Basic
import Std.Logic
import Mathlib.Tactic.Alias
import Mathlib.Tactic.Basic
import Mathlib.Tactic.SimpTrace
import Mathlib.Tactic.Relation.Symm
import Mathlib.Mathport.Attributes
import Mathlib.Mathport.Rename
import Mathlib.Tactic.Relation.Trans

universe u v w
-- implication
def Implies (a b : Prop) :=
  a → b

/-- Implication `→` is transitive. If `P → Q` and `Q → R` then `P → R`. -/
@[trans]
theorem Implies.trans {p q r : Prop} (h₁ : Implies p q) (h₂ : Implies q r) : Implies p r := fun hp => h₂ (h₁ hp)

def NonContradictory (a : Prop) : Prop :=
  ¬¬a

-- eq
-- proof irrelevance is built in
theorem proof_irrel {a : Prop} (h₁ h₂ : a) : h₁ = h₂ :=
  rfl

theorem trans_rel_left {α : Sort u} {a b c : α} (r : α → α → Prop) (h₁ : r a b) (h₂ : b = c) : r a c :=
  h₂ ▸ h₁

theorem trans_rel_right {α : Sort u} {a b c : α} (r : α → α → Prop) (h₁ : a = b) (h₂ : r b c) : r a c :=
  h₁.symm ▸ h₂

theorem not_of_eq_false {p : Prop} (h : p = False) : ¬p := fun hp => h ▸ hp

theorem cast_proof_irrel {α β : Sort u} (h₁ h₂ : α = β) (a : α) : cast h₁ a = cast h₂ a :=
  rfl

@[simp]
theorem Ne.def {α : Sort u} (a b : α) : (a ≠ b) = ¬a = b :=
  rfl

attribute [refl] HEq.refl

theorem eq_rec_heq {α : Sort u} {φ : α → Sort v} : ∀ {a a' : α} (h : a = a') (p : φ a), HEq (Eq.recOn h p : φ a') p
  | a, _, rfl, p => HEq.refl p

theorem heq_of_eq_rec_left {α : Sort u} {φ : α → Sort v} :
    ∀ {a a' : α} {p₁ : φ a} {p₂ : φ a'} (e : a = a') (h₂ : (Eq.recOn e p₁ : φ a') = p₂), HEq p₁ p₂
  | a, _, p₁, p₂, rfl, h => Eq.recOn h (HEq.refl p₁)

theorem heq_of_eq_rec_right {α : Sort u} {φ : α → Sort v} :
    ∀ {a a' : α} {p₁ : φ a} {p₂ : φ a'} (e : a' = a) (h₂ : p₁ = Eq.recOn e p₂), HEq p₁ p₂
  | a, _, p₁, p₂, rfl, h =>
    have : p₁ = p₂ := h
    this ▸ HEq.refl p₁

theorem of_heq_true {a : Prop} (h : HEq a True) : a :=
  of_eq_true (eq_of_heq h)

theorem eq_rec_compose :
    ∀ {α β φ : Sort u} (p₁ : β = φ) (p₂ : α = β) (a : α),
      (Eq.recOn p₁ (Eq.recOn p₂ a : β) : φ) = Eq.recOn (Eq.trans p₂ p₁) a
  | α, _, _, rfl, rfl, a => rfl

-- and
variable {a b c d : Prop}

-- Porting note: the order of arguments for `And.elim` has changed.
@[deprecated And.elim]
theorem And.elim' (h₁ : a ∧ b) (h₂ : a → b → c) : c :=
  And.elim h₂ h₁

#align and.elim And.elim'

-- xor
def Xor' (a b : Prop) :=
  a ∧ ¬b ∨ b ∧ ¬a


-- TODO where do we add `@[refl]` to `Iff.refl` (similarly symm and trans)

theorem not_of_not_not_not (h : ¬¬¬a) : ¬a := fun ha => absurd (not_not_intro ha) h

theorem and_implies (hac : a → c) (hbd : b → d) : a ∧ b → c ∧ d :=
  And.imp hac hbd

theorem and_comm' (a b : Prop) : a ∧ b ↔ b ∧ a :=
  and_comm

theorem and_assoc' (a b : Prop) : (a ∧ b) ∧ c ↔ a ∧ b ∧ c :=
  and_assoc

@[simp]
theorem and_true_iff (a : Prop) : a ∧ True ↔ a :=
  and_iff_left trivial

@[simp]
theorem true_and_iff (a : Prop) : True ∧ a ↔ a :=
  and_iff_right trivial

@[simp]
theorem and_false_iff (a : Prop) : a ∧ False ↔ False :=
  iff_false_intro And.right

@[simp]
theorem false_and_iff (a : Prop) : False ∧ a ↔ False :=
  iff_false_intro And.left

@[simp]
theorem and_self_iff (a : Prop) : a ∧ a ↔ a :=
  Iff.intro And.left fun h => ⟨h, h⟩

theorem or_comm' (a b : Prop) : a ∨ b ↔ b ∨ a :=
  or_comm

theorem or_assoc' (a b : Prop) : (a ∨ b) ∨ c ↔ a ∨ b ∨ c :=
  or_assoc

@[simp]
theorem or_true_iff (a : Prop) : a ∨ True ↔ True :=
  iff_true_intro (Or.inr trivial)

@[simp]
theorem true_or_iff (a : Prop) : True ∨ a ↔ True :=
  iff_true_intro (Or.inl trivial)

@[simp]
theorem or_false_iff (a : Prop) : a ∨ False ↔ a :=
  Iff.intro (Or.ndrec id False.elim) Or.inl

@[simp]
theorem false_or_iff (a : Prop) : False ∨ a ↔ a :=
  Iff.trans or_comm (or_false_iff a)

@[simp]
theorem or_self_iff (a : Prop) : a ∨ a ↔ a :=
  Iff.intro (Or.ndrec id id) Or.inl

theorem not_or_of_not {a b : Prop} : ¬a → ¬b → ¬(a ∨ b)
  | hna, hnb, Or.inl ha => absurd ha hna
  | hna, hnb, Or.inr hb => absurd hb hnb

-- iff simp rules
@[simp]
theorem iff_true_iff (a : Prop) : (a ↔ True) ↔ a :=
  Iff.intro (fun h => Iff.mpr h trivial) iff_true_intro

@[simp]
theorem true_iff_iff (a : Prop) : (True ↔ a) ↔ a :=
  Iff.trans Iff.comm (iff_true_iff a)

@[simp]
theorem iff_false_iff (a : Prop) : (a ↔ False) ↔ ¬a :=
  Iff.intro Iff.mp iff_false_intro

@[simp]
theorem false_iff_iff (a : Prop) : (False ↔ a) ↔ ¬a :=
  Iff.trans Iff.comm (iff_false_iff a)

@[simp]
theorem iff_self_iff (a : Prop) : (a ↔ a) ↔ True :=
  iff_true_intro Iff.rfl

-- attribute [intro] Exists.intro

-- exists unique
def ExistsUnique {α : Sort u} (p : α → Prop) :=
  ∃ x, p x ∧ ∀ y, p y → y = x

@[intro]
theorem ExistsUnique.intro {α : Sort u} {p : α → Prop} (w : α) (h₁ : p w) (h₂ : ∀ y, p y → y = w) : ∃! x, p x :=
  Exists.intro w ⟨h₁, h₂⟩

@[recursor 4]
theorem ExistsUnique.elim {α : Sort u} {p : α → Prop} {b : Prop} (h₂ : ∃! x, p x)
    (h₁ : ∀ x, p x → (∀ y, p y → y = x) → b) : b :=
  Exists.elim h₂ fun w hw => h₁ w (And.left hw) (And.right hw)

theorem exists_unique_of_exists_of_unique {α : Sort u} {p : α → Prop} (hex : ∃ x, p x)
    (hunique : ∀ y₁ y₂, p y₁ → p y₂ → y₁ = y₂) : ∃! x, p x :=
  Exists.elim hex fun x px => ExistsUnique.intro x px fun y => fun this : p y => hunique y x this px

theorem exists {α : Sort u} {p : α → Prop} (h : ∃! x, p x) : ∃ x, p x :=
  Exists.elim h fun x hx => ⟨x, And.left hx⟩

theorem unique {α : Sort u} {p : α → Prop} (h : ∃! x, p x) {y₁ y₂ : α} (py₁ : p y₁) (py₂ : p y₂) : y₁ = y₂ :=
  ExistsUnique.elim h fun x => fun this : p x => fun unique : ∀ y, p y → y = x =>
    show y₁ = y₂ from Eq.trans (unique _ py₁) (Eq.symm (unique _ py₂))

@[congr]
theorem exists_unique_congr {α : Sort u} {p₁ p₂ : α → Prop} (h : ∀ x, p₁ x ↔ p₂ x) : ExistsUnique p₁ ↔ ∃! x, p₂ x :=
  --
    exists_congr
    fun x => and_congr (h x) (forall_congr' fun y => imp_congr (h y) Iff.rfl)

export Decidable (isTrue isFalse toBool)

@[simp]
theorem decide_True' (h : Decidable True) : @decide True h = tt :=
  Decidable.casesOn h (fun h => False.elim (Iff.mp not_true h)) fun _ => rfl

@[simp]
theorem decide_False' (h : Decidable False) : @decide False h = ff :=
  Decidable.casesOn h (fun h => rfl) fun h => False.elim h

instance Decidable.true : Decidable True :=
  isTrue trivial

instance Decidable.false : Decidable False :=
  isFalse not_false

namespace Decidable

variable {p q : Prop}

def recOn_true [h : Decidable p] {h₁ : p → Sort u} {h₂ : ¬p → Sort u} (h₃ : p) (h₄ : h₁ h₃) : Decidable.recOn h h₂ h₁ :=
  Decidable.recOn h (fun h => False.ndrec _ (h h₃)) fun h => h₄

def recOn_false [h : Decidable p] {h₁ : p → Sort u} {h₂ : ¬p → Sort u} (h₃ : ¬p) (h₄ : h₂ h₃) :
    Decidable.recOn h h₂ h₁ :=
  Decidable.recOn h (fun h => h₄) fun h => False.ndrec _ (h₃ h)

def byCases {q : Sort u} [φ : Decidable p] : (p → q) → (¬p → q) → q :=
  dite _

theorem by_contradiction [Decidable p] (h : ¬p → False) : p :=
  if h₁ : p then h₁ else False.ndrec _ (h h₁)

theorem not_not_iff (p) [Decidable p] : ¬¬p ↔ p :=
  Iff.intro of_not_not not_not_intro

theorem not_or_iff_and_not (p q) [d₁ : Decidable p] [d₂ : Decidable q] : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  Iff.intro
    (fun h =>
      match d₁ with
      | is_true h₁ => False.elim <| h (Or.inl h₁)
      | is_false h₁ =>
        match d₂ with
        | is_true h₂ => False.elim <| h (Or.inr h₂)
        | is_false h₂ => ⟨h₁, h₂⟩)
    fun ⟨np, nq⟩ h => Or.elim h np nq

end Decidable

section

variable {p q : Prop}

instance [Decidable p] [Decidable q] : Decidable (p ∧ q) :=
  if hp : p then if hq : q then isTrue ⟨hp, hq⟩ else isFalse fun h : p ∧ q => hq (And.right h)
  else isFalse fun h : p ∧ q => hp (And.left h)

instance [Decidable p] [Decidable q] : Decidable (p ∨ q) :=
  if hp : p then isTrue (Or.inl hp) else if hq : q then isTrue (Or.inr hq) else isFalse (Or.ndrec hp hq)

instance [Decidable p] : Decidable ¬p :=
  if hp : p then isFalse (absurd hp) else isTrue hp

instance Implies.decidable [Decidable p] [Decidable q] : Decidable (p → q) :=
  if hp : p then if hq : q then isTrue fun h => hq else isFalse fun h : p → q => absurd (h hp) hq
  else isTrue fun h => absurd h hp

instance [Decidable p] [Decidable q] : Decidable (p ↔ q) :=
  if hp : p then if hq : q then isTrue ⟨fun _ => hq, fun _ => hp⟩ else is_false fun h => hq (h.1 hp)
  else if hq : q then is_false fun h => hp (h.2 hq) else is_true <| ⟨fun h => absurd h hp, fun h => absurd h hq⟩

instance [Decidable p] [Decidable q] : Decidable (Xor' p q) :=
  if hp : p then
    if hq : q then isFalse (Or.ndrec (fun ⟨_, h⟩ => h hq : ¬(p ∧ ¬q)) (fun ⟨_, h⟩ => h hp : ¬(q ∧ ¬p)))
    else is_true <| Or.inl ⟨hp, hq⟩
  else
    if hq : q then is_true <| Or.inr ⟨hq, hp⟩
    else isFalse (Or.ndrec (fun ⟨h, _⟩ => hp h : ¬(p ∧ ¬q)) (fun ⟨h, _⟩ => hq h : ¬(q ∧ ¬p)))

instance existsPropDecidable {p} (P : p → Prop) [Dp : Decidable p] [DP : ∀ h, Decidable (P h)] : Decidable (∃ h, P h) :=
  if h : p then decidable_of_decidable_of_iff (DP h) ⟨fun h2 => ⟨h, h2⟩, fun ⟨h', h2⟩ => h2⟩
  else isFalse (mt (fun ⟨h, _⟩ => h) h)

instance forallPropDecidable {p} (P : p → Prop) [Dp : Decidable p] [DP : ∀ h, Decidable (P h)] : Decidable (∀ h, P h) :=
  if h : p then decidable_of_decidable_of_iff (DP h) ⟨fun h2 _ => h2, fun al => al h⟩ else isTrue fun h2 => absurd h2 h

end

instance {α : Sort u} [DecidableEq α] (a b : α) : Decidable (a ≠ b) :=
  Implies.decidable

def IsDecEq {α : Sort u} (p : α → α → Bool) : Prop :=
  ∀ ⦃x y : α⦄, p x y = tt → x = y

def IsDecRefl {α : Sort u} (p : α → α → Bool) : Prop :=
  ∀ x, p x x = tt

open Decidable

instance : DecidableEq Bool
  | ff, ff => isTrue rfl
  | ff, tt => isFalse Bool.ff_ne_tt
  | tt, ff => isFalse (Ne.symm Bool.ff_ne_tt)
  | tt, tt => isTrue rfl

def decidable_eq_of_bool_pred {α : Sort u} {p : α → α → Bool} (h₁ : IsDecEq p) (h₂ : IsDecRefl p) : DecidableEq α :=
  fun x y : α =>
  if hp : p x y = tt then isTrue (h₁ hp)
  else isFalse fun hxy : x = y => absurd (h₂ y) (@Eq.recOn _ _ (fun z => ¬p z y = tt) _ hxy hp)

theorem decidable_eq_inl_refl {α : Sort u} [h : DecidableEq α] (a : α) : h a a = isTrue (Eq.refl a) :=
  match h a a with
  | is_true e => rfl
  | is_false n => absurd rfl n

theorem decidable_eq_inr_neg {α : Sort u} [h : DecidableEq α] {a b : α} : ∀ n : a ≠ b, h a b = isFalse n := fun n =>
  match h a b with
  | is_true e => absurd e n
  | is_false n₁ => proof_irrel n n₁ ▸ Eq.refl (isFalse n)

theorem rec_subsingleton {p : Prop} [h : Decidable p] {h₁ : p → Sort u} {h₂ : ¬p → Sort u}
    [h₃ : ∀ h : p, Subsingleton (h₁ h)] [h₄ : ∀ h : ¬p, Subsingleton (h₂ h)] : Subsingleton (Decidable.recOn h h₂ h₁) :=
  match h with
  | is_true h => h₃ h
  | is_false h => h₄ h

@[simp]
theorem if_t_t (c : Prop) [h : Decidable c] {α : Sort u} (t : α) : ite c t t = t :=
  match h with
  | is_true hc => rfl
  | is_false hnc => rfl

theorem imp_of_if_pos {c t e : Prop} [Decidable c] (h : ite c t e) : c → t := fun hc =>
  Eq.recOn (if_pos hc : ite c t e = t) h

theorem imp_of_if_neg {c t e : Prop} [Decidable c] (h : ite c t e) : ¬c → e := fun hnc =>
  Eq.recOn (if_neg hnc : ite c t e = e) h

theorem if_ctx_congr {α : Sort u} {b c : Prop} [dec_b : Decidable b] [dec_c : Decidable c] {x y u v : α} (h_c : b ↔ c)
    (h_t : c → x = u) (h_e : ¬c → y = v) : ite b x y = ite c u v :=
  match dec_b, dec_c with
  | is_false h₁, is_false h₂ => h_e h₂
  | is_true h₁, is_true h₂ => h_t h₂
  | is_false h₁, is_true h₂ => absurd h₂ (Iff.mp (not_congr h_c) h₁)
  | is_true h₁, is_false h₂ => absurd h₁ (Iff.mpr (not_congr h_c) h₂)

theorem if_congr {α : Sort u} {b c : Prop} [dec_b : Decidable b] [dec_c : Decidable c] {x y u v : α} (h_c : b ↔ c)
    (h_t : x = u) (h_e : y = v) : ite b x y = ite c u v :=
  @if_ctx_congr α b c dec_b dec_c x y u v h_c (fun h => h_t) fun h => h_e

theorem if_ctx_congr_prop {b c x y u v : Prop} [dec_b : Decidable b] [dec_c : Decidable c] (h_c : b ↔ c)
    (h_t : c → (x ↔ u)) (h_e : ¬c → (y ↔ v)) : ite b x y ↔ ite c u v :=
  match dec_b, dec_c with
  | is_false h₁, is_false h₂ => h_e h₂
  | is_true h₁, is_true h₂ => h_t h₂
  | is_false h₁, is_true h₂ => absurd h₂ (Iff.mp (not_congr h_c) h₁)
  | is_true h₁, is_false h₂ => absurd h₁ (Iff.mpr (not_congr h_c) h₂)

@[congr]
theorem if_congr_prop {b c x y u v : Prop} [dec_b : Decidable b] [dec_c : Decidable c] (h_c : b ↔ c) (h_t : x ↔ u)
    (h_e : y ↔ v) : ite b x y ↔ ite c u v :=
  if_ctx_congr_prop h_c (fun h => h_t) fun h => h_e

theorem if_ctx_simp_congr_prop {b c x y u v : Prop} [dec_b : Decidable b] (h_c : b ↔ c) (h_t : c → (x ↔ u))
    (h_e : ¬c → (y ↔ v)) : ite b x y ↔ @ite Prop c (decidable_of_decidable_of_iff dec_b h_c) u v :=
  @if_ctx_congr_prop b c x y u v dec_b (decidable_of_decidable_of_iff dec_b h_c) h_c h_t h_e

@[congr]
theorem if_simp_congr_prop {b c x y u v : Prop} [dec_b : Decidable b] (h_c : b ↔ c) (h_t : x ↔ u) (h_e : y ↔ v) :
    ite b x y ↔ @ite Prop c (decidable_of_decidable_of_iff dec_b h_c) u v :=
  @if_ctx_simp_congr_prop b c x y u v dec_b h_c (fun h => h_t) fun h => h_e

@[congr]
theorem dif_ctx_congr {α : Sort u} {b c : Prop} [dec_b : Decidable b] [dec_c : Decidable c] {x : b → α} {u : c → α}
    {y : ¬b → α} {v : ¬c → α} (h_c : b ↔ c) (h_t : ∀ h : c, x (Iff.mpr h_c h) = u h)
    (h_e : ∀ h : ¬c, y (Iff.mpr (not_congr h_c) h) = v h) : @dite α b dec_b x y = @dite α c dec_c u v :=
  match dec_b, dec_c with
  | is_false h₁, is_false h₂ => h_e h₂
  | is_true h₁, is_true h₂ => h_t h₂
  | is_false h₁, is_true h₂ => absurd h₂ (Iff.mp (not_congr h_c) h₁)
  | is_true h₁, is_false h₂ => absurd h₁ (Iff.mpr (not_congr h_c) h₂)

theorem dif_ctx_simp_congr {α : Sort u} {b c : Prop} [dec_b : Decidable b] {x : b → α} {u : c → α} {y : ¬b → α}
    {v : ¬c → α} (h_c : b ↔ c) (h_t : ∀ h : c, x (Iff.mpr h_c h) = u h)
    (h_e : ∀ h : ¬c, y (Iff.mpr (not_congr h_c) h) = v h) :
    @dite α b dec_b x y = @dite α c (decidable_of_decidable_of_iff dec_b h_c) u v :=
  @dif_ctx_congr α b c dec_b (decidable_of_decidable_of_iff dec_b h_c) x u y v h_c h_t h_e

def AsTrue (c : Prop) [Decidable c] : Prop :=
  if c then True else False

def AsFalse (c : Prop) [Decidable c] : Prop :=
  if c then False else True

theorem get {c : Prop} [h₁ : Decidable c] (h₂ : AsTrue c) : c :=
  match h₁, h₂ with
  | is_true h_c, h₂ => h_c
  | is_false h_c, h₂ => False.elim h₂

-- Equalities for rewriting let-expressions
theorem let_value_eq {α : Sort u} {β : Sort v} {a₁ a₂ : α} (b : α → β) :
    a₁ = a₂ →
      (let x : α := a₁
        b x) =
        let x : α := a₂
        b x :=
  fun h => Eq.recOn h rfl

theorem let_value_heq {α : Sort v} {β : α → Sort u} {a₁ a₂ : α} (b : ∀ x : α, β x) :
    a₁ = a₂ →
      HEq
        (let x : α := a₁
        b x)
        (let x : α := a₂
        b x) :=
  fun h => Eq.recOn h (HEq.refl (b a₁))

theorem let_body_eq {α : Sort v} {β : α → Sort u} (a : α) {b₁ b₂ : ∀ x : α, β x} :
    (∀ x, b₁ x = b₂ x) →
      (let x : α := a
        b₁ x) =
        let x : α := a
        b₂ x :=
  fun h => h a

theorem let_eq {α : Sort v} {β : Sort u} {a₁ a₂ : α} {b₁ b₂ : α → β} :
    a₁ = a₂ →
      (∀ x, b₁ x = b₂ x) →
        (let x : α := a₁
          b₁ x) =
          let x : α := a₂
          b₂ x :=
  fun h₁ h₂ => Eq.recOn h₁ (h₂ a₁)

section Relation

variable {α : Sort u} {β : Sort v} (r : β → β → Prop)

/-- Temporary notation for a relation. -/
local infixl:50 "≺" => r

def Reflexive :=
  ∀ x, x≺x

def Symmetric :=
  ∀ ⦃x y⦄, x≺y → y≺x

def Transitive :=
  ∀ ⦃x y z⦄, x≺y → y≺z → x≺z

def Equivalence :=
  Reflexive r ∧ Symmetric r ∧ Transitive r

def Total :=
  ∀ x y, x≺y ∨ y≺x

theorem mk (rfl : Reflexive r) (symm : Symmetric r) (trans : Transitive r) : Equivalence r :=
  ⟨rfl, symm, trans⟩

def Irreflexive :=
  ∀ x, ¬x≺x

def AntiSymmetric :=
  ∀ ⦃x y⦄, x≺y → y≺x → x = y

def EmptyRelation := fun a₁ a₂ : α => False

def Subrelation (q r : β → β → Prop) :=
  ∀ ⦃x y⦄, q x y → r x y

def InvImage (f : α → β) : α → α → Prop := fun a₁ a₂ => f a₁≺f a₂

theorem InvImage.trans (f : α → β) (h : Transitive r) : Transitive (InvImage r f) :=
  fun (a₁ a₂ a₃ : α) (h₁ : InvImage r f a₁ a₂) (h₂ : InvImage r f a₂ a₃) => h h₁ h₂

theorem InvImage.irreflexive (f : α → β) (h : Irreflexive r) : Irreflexive (InvImage r f) :=
  fun (a : α) (h₁ : InvImage r f a a) => h (f a) h₁

end Relation

section Binary

variable {α : Type u} {β : Type v}

variable (f : α → α → α)

variable (inv : α → α)

variable (one : α)

local notation a "*" b => f a b

local notation a "⁻¹" => inv a

variable (g : α → α → α)

local notation a "+" b => g a b

def Commutative :=
  ∀ a b, (a*b) = b*a

def Associative :=
  ∀ a b c, ((a*b)*c) = a*b*c

def LeftIdentity :=
  ∀ a, (one*a) = a

def RightIdentity :=
  ∀ a, (a*one) = a

def RightInverse :=
  ∀ a, (a*a⁻¹) = one

def LeftCancelative :=
  ∀ a b c, ((a*b) = a*c) → b = c

def RightCancelative :=
  ∀ a b c, ((a*b) = c*b) → a = c

def LeftDistributive :=
  ∀ a b c, (a*b+c) = (a*b)+a*c

def RightDistributive :=
  ∀ a b c, ((a+b)*c) = (a*c)+b*c

def RightCommutative (h : β → α → β) :=
  ∀ b a₁ a₂, h (h b a₁) a₂ = h (h b a₂) a₁

def LeftCommutative (h : α → β → β) :=
  ∀ a₁ a₂ b, h a₁ (h a₂ b) = h a₂ (h a₁ b)

theorem left_comm : Commutative f → Associative f → LeftCommutative f := fun hcomm hassoc => fun a b c =>
  calc
    (a*b*c) = (a*b)*c := Eq.symm (hassoc a b c)
    _ = (b*a)*c := hcomm a b ▸ rfl
    _ = b*a*c := hassoc b a c


theorem right_comm : Commutative f → Associative f → RightCommutative f := fun hcomm hassoc => fun a b c =>
  calc
    ((a*b)*c) = a*b*c := hassoc a b c
    _ = a*c*b := hcomm b c ▸ rfl
    _ = (a*c)*b := Eq.symm (hassoc a c b)


end Binary



--- Old ad-hoc port:

#align opt_param_eq optParam_eq

/- Implication -/

@[deprecated] def Implies (a b : Prop) := a → b

/-- Implication `→` is transitive. If `P → Q` and `Q → R` then `P → R`. -/
-- FIXME This should have `@[trans]`, but the `trans` attributed PR'd in #253 rejects it.
@[deprecated] theorem Implies.trans {p q r : Prop} (h₁ : p → q) (h₂ : q → r) :
    p → r := fun hp => h₂ (h₁ hp)

/- Not -/

@[deprecated] def NonContradictory (a : Prop) : Prop := ¬¬a

#align non_contradictory_intro not_not_intro

/- Eq -/

alias proofIrrel ← proof_irrel
alias congrFun ← congr_fun
alias congrArg ← congr_arg

@[deprecated] theorem trans_rel_left {α : Sort u} {a b c : α}
    (r : α → α → Prop) (h₁ : r a b) (h₂ : b = c) : r a c := h₂ ▸ h₁

@[deprecated] theorem trans_rel_right {α : Sort u} {a b c : α}
    (r : α → α → Prop) (h₁ : a = b) (h₂ : r b c) : r a c := h₁ ▸ h₂

theorem not_of_eq_false {p : Prop} (h : p = False) : ¬p := fun hp => h ▸ hp

theorem cast_proof_irrel (h₁ h₂ : α = β) (a : α) : cast h₁ a = cast h₂ a := rfl

/- Ne -/

theorem Ne.def {α : Sort u} (a b : α) : (a ≠ b) = ¬ (a = b) := rfl

attribute [symm] Ne.symm

/- HEq -/

alias eqRec_heq ← eq_rec_heq

-- FIXME
-- attribute [refl] HEq.refl
-- attribute [symm] HEq.symm
-- attribute [trans] HEq.trans
-- attribute [trans] heq_of_eq_of_heq

theorem heq_of_eq_rec_left {φ : α → Sort v} {a a' : α} {p₁ : φ a} {p₂ : φ a'} :
    (e : a = a') → (h₂ : Eq.rec (motive := fun a _ => φ a) p₁ e = p₂) → HEq p₁ p₂
  | rfl, rfl => HEq.rfl

theorem heq_of_eq_rec_right {φ : α → Sort v} {a a' : α} {p₁ : φ a} {p₂ : φ a'} :
    (e : a' = a) → (h₂ : p₁ = Eq.rec (motive := fun a _ => φ a) p₂ e) → HEq p₁ p₂
  | rfl, rfl => HEq.rfl

theorem of_heq_true {a : Prop} (h : HEq a True) : a := of_eq_true (eq_of_heq h)

theorem eq_rec_compose {α β φ : Sort u} :
    ∀ (p₁ : β = φ) (p₂ : α = β) (a : α),
      (Eq.recOn p₁ (Eq.recOn p₂ a : β) : φ) = Eq.recOn (Eq.trans p₂ p₁) a
  | rfl, rfl, _ => rfl

/- and -/

variable {a b c d : Prop}

#align and.symm And.symm
#align and.swap And.symm

/- or -/

#align non_contradictory_em not_not_em
#align or.symm Or.symm
#align or.swap Or.symm

/- xor -/

def Xor' (a b : Prop) := (a ∧ ¬ b) ∨ (b ∧ ¬ a)
#align xor Xor'

/- iff -/

#align iff.mp Iff.mp
#align iff.elim_left Iff.mp
#align iff.mpr Iff.mpr
#align iff.elim_right Iff.mpr

-- FIXME
-- attribute [refl] Iff.refl
-- attribute [trans] Iff.trans
-- attribute [symm] Iff.symm

-- This is needed for `calc` to work with `iff`.
instance : Trans Iff Iff Iff where
  trans := fun p q => p.trans q

#align not_congr not_congr
#align not_iff_not_of_iff not_congr
#align not_non_contradictory_iff_absurd not_not_not

alias not_not_not ↔ not_of_not_not_not _

-- FIXME
-- attribute [congr] not_congr

@[deprecated and_comm] theorem and_comm' (a b) : a ∧ b ↔ b ∧ a := and_comm
#align and.comm and_comm
#align and_comm and_comm'

@[deprecated and_assoc] theorem and_assoc' (a b) : (a ∧ b) ∧ c ↔ a ∧ (b ∧ c) := and_assoc
#align and_assoc and_assoc'
#align and.assoc and_assoc

#align and.left_comm and_left_comm

#align and_iff_left and_iff_leftₓ -- reorder implicits

-- FIXME: remove _iff and add _eq for the lean 4 core versions
theorem and_true_iff : p ∧ True ↔ p := iff_of_eq (and_true _)
#align and_true and_true_iff
theorem true_and_iff : True ∧ p ↔ p := iff_of_eq (true_and _)
#align true_and true_and_iff
theorem and_false_iff : p ∧ False ↔ False := iff_of_eq (and_false _)
#align and_false and_false_iff
theorem false_and_iff : False ∧ p ↔ False := iff_of_eq (false_and _)
#align false_and false_and_iff
#align not_and_self not_and_self_iff
#align and_not_self and_not_self_iff
theorem and_self_iff : p ∧ p ↔ p := iff_of_eq (and_self _)
#align and_self and_self_iff

#align or.imp Or.impₓ -- reorder implicits

#align and.elim And.elimₓ
#align iff.elim Iff.elimₓ
#align imp_congr imp_congrₓ
#align imp_congr_ctx imp_congr_ctxₓ
#align imp_congr_right imp_congr_rightₓ

#align eq_true_intro eq_true
#align eq_false_intro eq_false
#align eq_false eq_false_eq
#align eq_true eq_true_eq

@[deprecated or_comm] theorem or_comm' (a b) : a ∨ b ↔ b ∨ a := or_comm
#align or.comm or_comm
#align or_comm or_comm'

@[deprecated or_assoc] theorem or_assoc' (a b) : (a ∨ b) ∨ c ↔ a ∨ (b ∨ c) := or_assoc
#align or.assoc or_assoc
#align or_assoc or_assoc'

#align or_left_comm or_left_comm
#align or.left_comm or_left_comm

#align or_iff_left_of_imp or_iff_left_of_impₓ -- reorder implicits

theorem true_or_iff : True ∨ p ↔ True := iff_of_eq (true_or _)
#align true_or true_or_iff
theorem or_true_iff : p ∨ True ↔ True := iff_of_eq (or_true _)
#align or_true or_true_iff
theorem false_or_iff : False ∨ p ↔ p := iff_of_eq (false_or _)
#align false_or false_or_iff
theorem or_false_iff : p ∨ False ↔ p := iff_of_eq (or_false _)
#align or_false or_false_iff
theorem or_self_iff : p ∨ p ↔ p := iff_of_eq (or_self _)
#align or_self or_self_iff

theorem not_or_of_not : ¬a → ¬b → ¬(a ∨ b) := fun h1 h2 => not_or.2 ⟨h1, h2⟩
#align not_or not_or_of_not

theorem iff_true_iff : (a ↔ True) ↔ a := iff_of_eq (iff_true _)
#align iff_true iff_true_iff
theorem true_iff_iff : (True ↔ a) ↔ a := iff_of_eq (true_iff _)
#align true_iff true_iff_iff

theorem iff_false_iff : (a ↔ False) ↔ ¬a := iff_of_eq (iff_false _)
#align iff_false iff_false_iff

theorem false_iff_iff : (False ↔ a) ↔ ¬a := iff_of_eq (false_iff _)
#align false_iff false_iff_iff

theorem iff_self_iff (a : Prop) : (a ↔ a) ↔ True := iff_of_eq (iff_self _)
#align iff_self iff_self_iff

#align iff_congr iff_congrₓ -- reorder implicits

#align implies_true_iff imp_true_iff
#align false_implies_iff false_imp_iff
#align true_implies_iff true_imp_iff

#align Exists Exists -- otherwise it would get the name ExistsCat

-- TODO
-- attribute [intro] Exists.intro

/- exists unique -/

def ExistsUnique (p : α → Prop) := ∃ x, p x ∧ ∀ y, p y → y = x

open Lean TSyntax.Compat in
macro "∃! " xs:explicitBinders ", " b:term : term => expandExplicitBinders ``ExistsUnique xs b

/-- Pretty-printing for `ExistsUnique`, following the same pattern as pretty printing
    for `Exists`. -/
@[app_unexpander ExistsUnique] def unexpandExistsUnique : Lean.PrettyPrinter.Unexpander
  | `($(_) fun $x:ident => ∃! $xs:binderIdent*, $b) => `(∃! $x:ident $xs:binderIdent*, $b)
  | `($(_) fun $x:ident => $b)                      => `(∃! $x:ident, $b)
  | `($(_) fun ($x:ident : $t) => $b)               => `(∃! ($x:ident : $t), $b)
  | _                                               => throw ()

-- @[intro] -- TODO
theorem ExistsUnique.intro {p : α → Prop} (w : α)
    (h₁ : p w) (h₂ : ∀ y, p y → y = w) : ∃! x, p x := ⟨w, h₁, h₂⟩

theorem ExistsUnique.elim {α : Sort u} {p : α → Prop} {b : Prop}
    (h₂ : ∃! x, p x) (h₁ : ∀ x, p x → (∀ y, p y → y = x) → b) : b :=
  Exists.elim h₂ (λ w hw => h₁ w (And.left hw) (And.right hw))

theorem exists_unique_of_exists_of_unique {α : Sort u} {p : α → Prop}
    (hex : ∃ x, p x) (hunique : ∀ y₁ y₂, p y₁ → p y₂ → y₁ = y₂) : ∃! x, p x :=
  Exists.elim hex (λ x px => ExistsUnique.intro x px (λ y (h : p y) => hunique y x h px))

theorem ExistsUnique.exists {p : α → Prop} : (∃! x, p x) → ∃ x, p x | ⟨x, h, _⟩ => ⟨x, h⟩
#align exists_of_exists_unique ExistsUnique.exists

theorem ExistsUnique.unique {α : Sort u} {p : α → Prop}
    (h : ∃! x, p x) {y₁ y₂ : α} (py₁ : p y₁) (py₂ : p y₂) : y₁ = y₂ :=
  let ⟨_, _, hy⟩ := h; (hy _ py₁).trans (hy _ py₂).symm
#align unique_of_exists_unique ExistsUnique.unique

/- exists, forall, exists unique congruences -/

-- TODO
-- attribute [congr] forall_congr'
-- attribute [congr] exists_congr'
#align forall_congr forall_congr'

#align Exists.imp Exists.imp
#align exists_imp_exists Exists.imp

-- @[congr]
theorem exists_unique_congr {p q : α → Prop} (h : ∀ a, p a ↔ q a) : (∃! a, p a) ↔ ∃! a, q a :=
  exists_congr fun _ => and_congr (h _) $ forall_congr' fun _ => imp_congr_left (h _)

/- decidable -/

#align decidable.to_bool Decidable.decide

theorem decide_True' (h : Decidable True) : decide True = true := by simp
#align to_bool_true_eq_tt decide_True'

theorem decide_False' (h : Decidable False) : decide False = false := by simp
#align to_bool_false_eq_ff decide_False'

namespace Decidable

def recOn_true [h : Decidable p] {h₁ : p → Sort u} {h₂ : ¬p → Sort u}
    (h₃ : p) (h₄ : h₁ h₃) : Decidable.recOn h h₂ h₁ :=
  cast (by match h with | .isTrue _ => rfl) h₄
#align decidable.rec_on_true Decidable.recOn_true

def recOn_false [h : Decidable p] {h₁ : p → Sort u} {h₂ : ¬p → Sort u} (h₃ : ¬p) (h₄ : h₂ h₃) :
    Decidable.recOn h h₂ h₁ :=
  cast (by match h with | .isFalse _ => rfl) h₄
#align decidable.rec_on_false Decidable.recOn_false

alias byCases ← by_cases
alias byContradiction ← by_contradiction
alias not_not ← not_not_iff

@[deprecated not_or] theorem not_or_iff_and_not (p q) [Decidable p] [Decidable q] :
    ¬(p ∨ q) ↔ ¬p ∧ ¬q := not_or

end Decidable

#align decidable_of_decidable_of_iff decidable_of_decidable_of_iff
#align decidable_of_decidable_of_eq decidable_of_decidable_of_eq
#align or.by_cases Or.by_cases

instance [Decidable p] [Decidable q] : Decidable (Xor' p q) := inferInstanceAs (Decidable (Or ..))

def IsDecEq {α : Sort u} (p : α → α → Bool) : Prop := ∀ ⦃x y : α⦄, p x y = true → x = y
def IsDecRefl {α : Sort u} (p : α → α → Bool) : Prop := ∀ x, p x x = true

def decidable_eq_of_bool_pred {α : Sort u} {p : α → α → Bool} (h₁ : IsDecEq p)
    (h₂ : IsDecRefl p) : DecidableEq α
  | x, y =>
    if hp : p x y = true then isTrue (h₁ hp)
    else isFalse (λ hxy : x = y => absurd (h₂ y) (by rwa [hxy] at hp))
#align decidable_eq_of_bool_pred decidable_eq_of_bool_pred

theorem decidable_eq_inl_refl {α : Sort u} [h : DecidableEq α] (a : α) :
    h a a = isTrue (Eq.refl a) :=
  match h a a with
  | isTrue _ => rfl

theorem decidable_eq_inr_neg {α : Sort u} [h : DecidableEq α] {a b : α}
    (n : a ≠ b) : h a b = isFalse n :=
  match h a b with
  | isFalse _ => rfl

#align inhabited.default Inhabited.default
#align arbitrary Inhabited.default

-- see Note [lower instance priority]
@[simp]
instance (priority := 100) nonempty_of_inhabited [Inhabited α] : Nonempty α :=
⟨default⟩

/- subsingleton -/

theorem rec_subsingleton {p : Prop} [h : Decidable p] {h₁ : p → Sort u} {h₂ : ¬p → Sort u}
    [h₃ : ∀ h : p, Subsingleton (h₁ h)] [h₄ : ∀ h : ¬p, Subsingleton (h₂ h)] :
    Subsingleton (Decidable.recOn h h₂ h₁) :=
  match h with
  | isTrue h => h₃ h
  | isFalse h => h₄ h

@[deprecated ite_self]
theorem if_t_t (c : Prop) [Decidable c] {α : Sort u} (t : α) : ite c t t = t := ite_self _

theorem imp_of_if_pos {c t e : Prop} [Decidable c] (h : ite c t e) (hc : c) : t :=
  by have := if_pos hc ▸ h; exact this
#align implies_of_if_pos imp_of_if_pos

theorem imp_of_if_neg {c t e : Prop} [Decidable c] (h : ite c t e) (hnc : ¬c) : e :=
  by have := if_neg hnc ▸ h; exact this
#align implies_of_if_neg imp_of_if_neg

theorem if_ctx_congr {α : Sort u} {b c : Prop} [dec_b : Decidable b] [dec_c : Decidable c]
    {x y u v : α} (h_c : b ↔ c) (h_t : c → x = u) (h_e : ¬c → y = v) : ite b x y = ite c u v :=
  match dec_b, dec_c with
  | isFalse _,  isFalse h₂ => h_e h₂
  | isTrue _,   isTrue h₂  => h_t h₂
  | isFalse h₁, isTrue h₂  => absurd h₂ (Iff.mp (not_congr h_c) h₁)
  | isTrue h₁,  isFalse h₂ => absurd h₁ (Iff.mpr (not_congr h_c) h₂)

theorem if_congr {α : Sort u} {b c : Prop} [Decidable b] [Decidable c]
    {x y u v : α} (h_c : b ↔ c) (h_t : x = u) (h_e : y = v) : ite b x y = ite c u v :=
  if_ctx_congr h_c (λ _ => h_t) (λ _ => h_e)

theorem if_ctx_congr_prop {b c x y u v : Prop} [dec_b : Decidable b] [dec_c : Decidable c]
    (h_c : b ↔ c) (h_t : c → (x ↔ u)) (h_e : ¬c → (y ↔ v)) : ite b x y ↔ ite c u v :=
  match dec_b, dec_c with
  | isFalse _,  isFalse h₂ => h_e h₂
  | isTrue _,   isTrue h₂  => h_t h₂
  | isFalse h₁, isTrue h₂  => absurd h₂ (Iff.mp (not_congr h_c) h₁)
  | isTrue h₁,  isFalse h₂ => absurd h₁ (Iff.mpr (not_congr h_c) h₂)

-- @[congr]
theorem if_congr_prop {b c x y u v : Prop} [Decidable b] [Decidable c] (h_c : b ↔ c) (h_t : x ↔ u)
    (h_e : y ↔ v) : ite b x y ↔ ite c u v :=
  if_ctx_congr_prop h_c (λ _ => h_t) (λ _ => h_e)

theorem if_ctx_simp_congr_prop {b c x y u v : Prop} [Decidable b] (h_c : b ↔ c) (h_t : c → (x ↔ u))
    (h_e : ¬c → (y ↔ v)) : ite b x y ↔ ite c (h := decidable_of_decidable_of_iff h_c) u v :=
  if_ctx_congr_prop (dec_c := decidable_of_decidable_of_iff h_c) h_c h_t h_e

theorem if_simp_congr_prop {b c x y u v : Prop} [Decidable b] (h_c : b ↔ c) (h_t : x ↔ u)
    (h_e : y ↔ v) : ite b x y ↔ (ite c (h := decidable_of_decidable_of_iff h_c) u v) :=
  if_ctx_simp_congr_prop h_c (λ _ => h_t) (λ _ => h_e)

-- @[congr]
theorem dif_ctx_congr {α : Sort u} {b c : Prop} [dec_b : Decidable b] [dec_c : Decidable c]
    {x : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}
    (h_c : b ↔ c) (h_t : ∀ h : c, x (Iff.mpr h_c h) = u h)
    (h_e : ∀ h : ¬c, y (Iff.mpr (not_congr h_c) h) = v h) :
    @dite α b dec_b x y = @dite α c dec_c u v :=
  match dec_b, dec_c with
  | isFalse _, isFalse h₂ => h_e h₂
  | isTrue _, isTrue h₂ => h_t h₂
  | isFalse h₁, isTrue h₂ => absurd h₂ (Iff.mp (not_congr h_c) h₁)
  | isTrue h₁, isFalse h₂ => absurd h₁ (Iff.mpr (not_congr h_c) h₂)

theorem dif_ctx_simp_congr {α : Sort u} {b c : Prop} [Decidable b]
    {x : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}
    (h_c : b ↔ c) (h_t : ∀ h : c, x (Iff.mpr h_c h) = u h)
    (h_e : ∀ h : ¬c, y (Iff.mpr (not_congr h_c) h) = v h) :
    dite b x y = dite c (h := decidable_of_decidable_of_iff h_c) u v :=
  dif_ctx_congr (dec_c := decidable_of_decidable_of_iff h_c) h_c h_t h_e

def AsTrue (c : Prop) [Decidable c] : Prop := if c then True else False

def AsFalse (c : Prop) [Decidable c] : Prop := if c then False else True

theorem AsTrue.get {c : Prop} [h₁ : Decidable c] (_ : AsTrue c) : c :=
  match h₁ with
  | isTrue h_c => h_c
#align of_as_true AsTrue.get

#align ulift ULift
#align plift PLift

/- Equalities for rewriting let-expressions -/
theorem let_value_eq {α : Sort u} {β : Sort v} {a₁ a₂ : α} (b : α → β)
    (h : a₁ = a₂) : (let x : α := a₁; b x) = (let x : α := a₂; b x) := congrArg b h

theorem let_value_heq {α : Sort v} {β : α → Sort u} {a₁ a₂ : α} (b : ∀ x : α, β x)
    (h : a₁ = a₂) : HEq (let x : α := a₁; b x) (let x : α := a₂; b x) := by cases h; rfl
#align let_value_heq let_value_heq -- FIXME: mathport thinks this is a dubious translation

theorem let_body_eq {α : Sort v} {β : α → Sort u} (a : α) {b₁ b₂ : ∀ x : α, β x}
    (h : ∀ x, b₁ x = b₂ x) : (let x : α := a; b₁ x) = (let x : α := a; b₂ x) := by exact h _ ▸ rfl
#align let_value_eq let_value_eq -- FIXME: mathport thinks this is a dubious translation

theorem let_eq {α : Sort v} {β : Sort u} {a₁ a₂ : α} {b₁ b₂ : α → β}
    (h₁ : a₁ = a₂) (h₂ : ∀ x, b₁ x = b₂ x) :
    (let x : α := a₁; b₁ x) = (let x : α := a₂; b₂ x) := by simp [h₁, h₂]
#align let_eq let_eq -- FIXME: mathport thinks this is a dubious translation

section Relation

variable {α : Sort u} {β : Sort v} (r : β → β → Prop)

/-- Local notation for an arbitrary binary relation `r`. -/
local infix:50 " ≺ " => r

/-- A reflexive relation relates every element to itself. -/
def Reflexive := ∀ x, x ≺ x

/-- A relation is symmetric if `x ≺ y` implies `y ≺ x`. -/
def Symmetric := ∀ ⦃x y⦄, x ≺ y → y ≺ x

/-- A relation is transitive if `x ≺ y` and `y ≺ z` together imply `x ≺ z`. -/
def Transitive := ∀ ⦃x y z⦄, x ≺ y → y ≺ z → x ≺ z

/-- A relation is total if for all `x` and `y`, either `x ≺ y` or `y ≺ x`. -/
def Total := ∀ x y, x ≺ y ∨ y ≺ x

#align mk_equivalence Equivalence.mk

/-- Irreflexive means "not reflexive". -/
def Irreflexive := ∀ x, ¬ x ≺ x

/-- A relation is antisymmetric if `x ≺ y` and `y ≺ x` together imply that `x = y`. -/
def AntiSymmetric := ∀ ⦃x y⦄, x ≺ y → y ≺ x → x = y

/-- An empty relation does not relate any elements. -/
@[nolint unusedArguments]
def EmptyRelation := λ _ _ : α => False

theorem InvImage.trans (f : α → β) (h : Transitive r) : Transitive (InvImage r f) :=
  fun (a₁ a₂ a₃ : α) (h₁ : InvImage r f a₁ a₂) (h₂ : InvImage r f a₂ a₃) => h h₁ h₂

theorem InvImage.irreflexive (f : α → β) (h : Irreflexive r) : Irreflexive (InvImage r f) :=
  fun (a : α) (h₁ : InvImage r f a a) => h (f a) h₁

end Relation

section Binary

variable {α : Type u} {β : Type v} (f : α → α → α) (inv : α → α) (one : α)

/-- Local notation for `f`, high priority to avoid ambiguity with `HMul.hMul`. -/
local infix:70 (priority := high) " * " => f

/-- Local notation for `inv`, high priority to avoid ambiguity with `Inv.inv`. -/
local postfix:100 (priority := high) "⁻¹" => inv

variable (g : α → α → α)

/-- Local notation for `g`, high priority to avoid ambiguity with `HAdd.hAdd`. -/
local infix:65 (priority := high) " + " => g

def Commutative       := ∀ a b, a * b = b * a
def Associative       := ∀ a b c, (a * b) * c = a * (b * c)
def LeftIdentity      := ∀ a, one * a = a
def RightIdentity     := ∀ a, a * one = a
def RightInverse      := ∀ a, a * a⁻¹ = one
def LeftCancelative   := ∀ a b c, a * b = a * c → b = c
def RightCancelative  := ∀ a b c, a * b = c * b → a = c
def LeftDistributive  := ∀ a b c, a * (b + c) = a * b + a * c
def RightDistributive := ∀ a b c, (a + b) * c = a * c + b * c
def RightCommutative (h : β → α → β) := ∀ b a₁ a₂, h (h b a₁) a₂ = h (h b a₂) a₁
def LeftCommutative  (h : α → β → β) := ∀ a₁ a₂ b, h a₁ (h a₂ b) = h a₂ (h a₁ b)

theorem left_comm : Commutative f → Associative f → LeftCommutative f :=
  fun hcomm hassoc a b c => calc
    a*(b*c) = (a*b)*c := Eq.symm (hassoc a b c)
          _ = (b*a)*c := hcomm a b ▸ rfl
          _ = b*(a*c) := hassoc b a c

theorem right_comm : Commutative f → Associative f → RightCommutative f :=
  fun hcomm hassoc a b c => calc
    (a*b)*c = a*(b*c) := hassoc a b c
          _ = a*(c*b) := hcomm b c ▸ rfl
          _ = (a*c)*b := Eq.symm (hassoc a c b)

end Binary

namespace WellFounded

variable {α : Sort u} {C : α → Sort v} {r : α → α → Prop}

unsafe def fix'.impl (hwf : WellFounded r) (F : ∀ x, (∀ y, r y x → C y) → C x) (x : α) : C x :=
  F x fun y _ => impl hwf F y

@[implemented_by fix'.impl]
def fix' (hwf : WellFounded r) (F : ∀ x, (∀ y, r y x → C y) → C x) (x : α) : C x := hwf.fix F x

end WellFounded
