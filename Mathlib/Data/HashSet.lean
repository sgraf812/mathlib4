/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Data.HashMap

/-!
# `HashSet α` is implemented as `HashMap α Unit`

This is a minimal-effort implementation until it is done properly in `Std`.
-/

namespace Std

/--
A `HashSet`, implemented as `HashSet α := HashMap α Unit`.
-/
def HashSet (α : Type _) [BEq α] [Hashable α] := HashMap α Unit

namespace HashSet

variable {α : Type _} [BEq α] [Hashable α]

instance : Membership α (HashSet α) := ⟨fun a f => f.contains a⟩
instance {a : α} {s : HashSet α} : Decidable (a ∈ s) := sorry

def empty : HashSet α := HashMap.empty

/-- Construct a `HashSet` from a `List`, ignoring duplicates. -/
def ofList (L : List α) : HashSet α :=
  HashMap.ofList <| L.map (⟨·, ()⟩)

def insert (self : HashSet α) (a : α) : HashSet α := HashMap.insert self a ()

/-- Select only elements of a `HashSet` satisfying a predicate. -/
def filter (self : HashSet α) (p : α → Bool) : HashSet α :=
  self.filterKeys p

/-- Combine the elements of two `HashSet`s. -/
def union (f g : HashSet α) : HashSet α :=
  f.mergeWith (fun _ _ _ => ()) g

/-- `sdiff f g` returns the set of elements that are in `f` but not in `g`. -/
def sdiff (f g : HashSet α) : HashSet α :=
  f.filter (· ∉ g)
