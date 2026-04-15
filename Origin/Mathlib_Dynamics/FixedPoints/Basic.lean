/-
Extracted from Dynamics/FixedPoints/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Fixed points of a self-map

In this file we define

* the predicate `IsFixedPt f x := f x = x`;
* the set `fixedPoints f` of fixed points of a self-map `f`.

We also prove some simple lemmas about `IsFixedPt` and `∘`, `iterate`, and `Semiconj`.

## Tags

fixed point
-/

open Equiv

universe u v

variable {α : Type u} {β : Type v} {f fa g : α → α} {x : α} {fb : β → β} {e : Perm α}

namespace Function

open Function (Commute)

theorem isFixedPt_id (x : α) : IsFixedPt id x :=
  (rfl :)
