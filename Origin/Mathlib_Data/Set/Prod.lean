/-
Extracted from Data/Set/Prod.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Sets in product and pi types

This file proves basic properties of product of sets in `α × β` and in `Π i, α i`, and of the
diagonal of a type.

## Main declarations

This file contains basic results on the following notions, which are defined in `Set.Operations`.

* `Set.prod`: Binary product of sets. For `s : Set α`, `t : Set β`, we have
  `s.prod t : Set (α × β)`. Denoted by `s ×ˢ t`.
* `Set.diagonal`: Diagonal of a type. `Set.diagonal α = {(x, x) | x : α}`.
* `Set.offDiag`: Off-diagonal. `s ×ˢ s` without the diagonal.
* `Set.pi`: Arbitrary product of sets.
-/

open Function

namespace Set

/-! ### Cartesian binary product of sets -/

section Prod

variable {α β γ δ : Type*} {s s₁ s₂ : Set α} {t t₁ t₂ : Set β} {a : α} {b : β}

theorem Subsingleton.prod (hs : s.Subsingleton) (ht : t.Subsingleton) :
    (s ×ˢ t).Subsingleton := fun _x hx _y hy ↦
  Prod.ext (hs hx.1 hy.1) (ht hx.2 hy.2)

-- INSTANCE (free from Core): decidableMemProd
