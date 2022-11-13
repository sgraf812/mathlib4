/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

import Mathlib.Mathport.Rename

/-!  # Helper definitions and instances for `Ordering` -/

deriving instance Repr for Ordering

namespace Ordering

/-- Combine two `Ordering`s lexicographically. -/
@[inline]
def orElse : Ordering → Ordering → Ordering
  | lt, _ => lt
  | eq, o => o
  | gt, _ => gt

end Ordering

/--
Lift a decidable relation to an `Ordering`,
assuming that incomparable terms are `Ordering.eq`.
-/
def CmpUsing {α : Type u} (lt : α → α → Prop) [DecidableRel lt] (a b : α) : Ordering :=
  if lt a b then Ordering.lt else if lt b a then Ordering.gt else Ordering.eq
#align cmp_using CmpUsing

/--
Construct an `Ordering` from a type with a decidable `LT` instance,
assuming that incomparable terms are `Ordering.eq`.
-/
def Cmp {α : Type u} [LT α] [DecidableRel ((· < ·) : α → α → Prop)] (a b : α) : Ordering :=
  CmpUsing (· < ·) a b
#align cmp Cmp