/-
Extracted from Order/UpperLower/Prod.lean
Genuine: 3 of 4 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Upper and lower set product

The Cartesian product of sets carries over to upper and lower sets in a natural way. This file
defines said product over the types `UpperSet` and `LowerSet` and proves some of its properties.

## Notation

* `×ˢ` is notation for `UpperSet.prod` / `LowerSet.prod`.
-/

open Set

variable {α β : Type*}

section Preorder

variable [Preorder α] [Preorder β]

variable {s : Set α} {t : Set β}

theorem IsUpperSet.prod (hs : IsUpperSet s) (ht : IsUpperSet t) : IsUpperSet (s ×ˢ t) :=
  fun _ _ h ha => ⟨hs h.1 ha.1, ht h.2 ha.2⟩

theorem IsLowerSet.prod (hs : IsLowerSet s) (ht : IsLowerSet t) : IsLowerSet (s ×ˢ t) :=
  fun _ _ h ha => ⟨hs h.1 ha.1, ht h.2 ha.2⟩

end

namespace UpperSet

variable (s s₁ s₂ : UpperSet α) (t t₁ t₂ : UpperSet β) {x : α × β}

def prod : UpperSet (α × β) :=
  ⟨s ×ˢ t, s.2.prod t.2⟩

-- INSTANCE (free from Core): instSProd
