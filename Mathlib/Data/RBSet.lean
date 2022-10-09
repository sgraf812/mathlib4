/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Std.Data.RBMap

/-!
# `RBSet α`
-/

namespace Std


namespace RBSet

variable {α : Type _} {cmp : α → α → Ordering}

instance : Membership α (RBSet α cmp) := ⟨fun a f => f.contains a⟩
instance {a : α} {s : RBSet α cmp} : Decidable (a ∈ s) := sorry

/-- `s.filter p` returns the subset of the set `s` satisfying the predicate `p`. -/
def filter (self : RBSet α cmp) (p : α → Bool) : RBSet α cmp :=
  .ofList (self.toList.filter p) _

/-- `sdiff s t` returns the set of elements that are in `s` but not in `t`. -/
def sdiff (s t : RBSet α cmp) : RBSet α cmp :=
  s.filter (· ∉ t)
