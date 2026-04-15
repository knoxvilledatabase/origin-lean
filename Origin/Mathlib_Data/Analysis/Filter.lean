/-
Extracted from Data/Analysis/Filter.lean
Genuine: 2 of 5 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Computational realization of filters (experimental)

This file provides infrastructure to compute with filters.

## Main declarations

* `CFilter`: Realization of a filter base. Note that this is in the generality of filters on
  lattices, while `Filter` is filters of sets (so corresponding to `CFilter (Set α) σ`).
* `Filter.Realizer`: Realization of a `Filter`. `CFilter` that generates the given filter.
-/

open Set Filter

structure CFilter (α σ : Type*) [PartialOrder α] where
  f : σ → α
  pt : σ
  inf : σ → σ → σ
  inf_le_left : ∀ a b : σ, f (inf a b) ≤ f a
  inf_le_right : ∀ a b : σ, f (inf a b) ≤ f b

variable {α : Type*} {β : Type*} {σ : Type*} {τ : Type*}

-- INSTANCE (free from Core): [Inhabited

namespace CFilter

variable [PartialOrder α] (F : CFilter α σ)

-- INSTANCE (free from Core): :

def ofEquiv (E : σ ≃ τ) : CFilter α σ → CFilter α τ
  | ⟨f, p, g, h₁, h₂⟩ =>
    { f := fun a ↦ f (E.symm a)
      pt := E p
      inf := fun a b ↦ E (g (E.symm a) (E.symm b))
      inf_le_left := fun a b ↦ by simpa using h₁ (E.symm a) (E.symm b)
      inf_le_right := fun a b ↦ by simpa using h₂ (E.symm a) (E.symm b) }
