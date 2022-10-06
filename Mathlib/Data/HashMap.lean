/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Std.Data.HashMap
import Mathlib.Algebra.Group.Basic

/-!
# Algebraic structures on `HashMap`.

-/

open Std

variable [BEq α] [Hashable α] [DecidableEq β]

namespace Std.HashMap

/-- Pointwise addition of `HashMap`s. -/
def add [Zero β] [Add β] (f g : HashMap α β) : HashMap α β :=
  f.fold (fun h a b =>
    let b' := b + h.findD a 0
    if b' = 0 then h.erase a else h.insert a b') g

@[ext]
lemma ext {f g : HashMap α β} (w : ∀ a, f.find? a = g.find? a) : f = g := sorry

lemma ext_findD [Zero β] {f g : HashMap α β} (w : ∀ a, f.findD a 0 = g.findD a 0) : f = g := sorry

@[simp]
lemma findD_add [Zero β] [Add β] (f g : HashMap α β) (a : α) :
    (f.add g).findD a 0 = f.findD a 0 + g.findD a 0 :=
  sorry

instance [AddMonoid β] : AddMonoid (HashMap α β) :=
{ add := add,
  add_assoc := fun f g h => by
    apply ext_findD
    intro a
    sorry,
  zero := HashMap.empty,
  zero_add := sorry,
  add_zero := sorry,
  nsmul_zero' := sorry,
  nsmul_succ' := sorry, }
