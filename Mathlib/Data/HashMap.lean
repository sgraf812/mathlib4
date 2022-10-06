import Std.Data.HashMap
import Mathlib.Algebra.Group.Basic

open Std

variable [BEq α] [Hashable α] [AddMonoid β] [DecidableEq β]

namespace Std.HashMap

@[ext]
lemma ext {f g : HashMap α β} (w : ∀ a, f.find? a = g.find? a) : f = g := sorry

lemma ext_findD {f g : HashMap α β} (w : ∀ a, f.findD a 0 = g.findD a 0) : f = g := sorry

def add (f g : HashMap α β) : HashMap α β :=
  f.fold (fun h a b =>
    let b' := b + h.findD a 0
    if b' = 0 then h.erase a else h.insert a b') g

@[simp]
lemma findD_add (f g : HashMap α β) (a : α) : (f.add g).findD a 0 = f.findD a 0 + g.findD a 0 :=
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
