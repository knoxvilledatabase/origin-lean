/-
Extracted from Data/Set/Finite/Powerset.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Set.Finite.Basic

/-!
# Finiteness of the powerset of a finite set

## Implementation notes

Each result in this file should come in three forms: a `Fintype` instance, a `Finite` instance
and a `Set.Finite` constructor.

## Tags

finite sets
-/

open Set Function

universe u v w x

variable {α : Type u} {β : Type v} {ι : Sort w} {γ : Type x}

namespace Set

/-! ### Constructors for `Set.Finite`

Every constructor here should have a corresponding `Fintype` instance in the `Fintype` module.

The implementation of these constructors ideally should be no more than `Set.toFinite`,
after possibly setting up some `Fintype` and classical `Decidable` instances.
-/

section SetFiniteConstructors

theorem Finite.finite_subsets {α : Type u} {a : Set α} (h : a.Finite) : { b | b ⊆ a }.Finite := by
  convert ((Finset.powerset h.toFinset).map Finset.coeEmb.1).finite_toSet
  ext s
  simpa [← @exists_finite_iff_finset α fun t => t ⊆ a ∧ t = s, Finite.subset_toFinset,
    ← and_assoc, Finset.coeEmb] using h.subset

protected theorem Finite.powerset {s : Set α} (h : s.Finite) : (𝒫 s).Finite :=
  h.finite_subsets

end SetFiniteConstructors

end Set
