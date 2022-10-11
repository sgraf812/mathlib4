import Std.Data.RBMap

namespace Std.RBMap

def keys (m : RBMap α β cmp) : List α :=
m.foldr (fun k _ ks => k :: ks) []

def values (m : RBMap α β cmp) : List β :=
m.foldr (fun _ v vs => v :: vs) []

def mergeWith (f : α → β → β → β) (self other : RBMap α β cmp) : RBMap α β cmp :=
  other.foldl (init := self) fun m k v₂ =>
    match m.find? k with
    | none => m.insert k v₂
    | some v₁ => m.insert k (f k v₁ v₂)

def mapVal (self : RBMap α β cmp) (f : β → γ) : RBMap α γ cmp :=
  .ofList (self.toList.map (fun ⟨a, b⟩ => ⟨a, f b⟩)) _

instance [DecidableEq β] : DecidableEq (RBMap α β cmp) := sorry
