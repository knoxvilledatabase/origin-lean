/-
Extracted from NumberTheory/NumberField/InfinitePlace/Ramification.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Ramification of infinite places of a number field

This file studies the ramification of infinite places of a number field.

## Main Definitions and Results

* `NumberField.InfinitePlace.comap`: the restriction of an infinite place along an embedding.
* `NumberField.InfinitePlace.orbitRelEquiv`: the equiv between the orbits of infinite places under
  the action of the Galois group and the infinite places of the base field.
* `NumberField.InfinitePlace.IsUnramified`: an infinite place is unramified in a field extension
  if the restriction has the same multiplicity.
* `NumberField.InfinitePlace.not_isUnramified_iff`: an infinite place is not unramified
  (i.e., is ramified) iff it is a complex place above a real place.
* `NumberField.InfinitePlace.IsUnramifiedIn`: an infinite place of the base field is unramified
  in a field extension if every infinite place over it is unramified.
* `IsUnramifiedAtInfinitePlaces`: a field extension is unramified at infinite places if every
  infinite place is unramified.

## Tags

number field, infinite places, ramification
-/

open NumberField Fintype Module ComplexEmbedding

namespace NumberField.InfinitePlace

open scoped Finset

variable {k : Type*} [Field k] {K : Type*} [Field K] {F : Type*} [Field F]

def comap (w : InfinitePlace K) (f : k →+* K) : InfinitePlace k :=
  ⟨w.1.comp f.injective, w.embedding.comp f,
    by { ext x; change _ = w.1 (f x); rw [← w.2.choose_spec]; rfl }⟩
