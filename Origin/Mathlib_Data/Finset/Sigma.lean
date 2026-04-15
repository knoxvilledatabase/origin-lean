/-
Extracted from Data/Finset/Sigma.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Finite sets in a sigma type

This file defines a few `Finset` constructions on `Σ i, α i`.

## Main declarations

* `Finset.sigma`: Given a finset `s` in `ι` and finsets `t i` in each `α i`, `s.sigma t` is the
  finset of the dependent sum `Σ i, α i`
* `Finset.sigmaLift`: Lifts maps `α i → β i → Finset (γ i)` to a map
  `Σ i, α i → Σ i, β i → Finset (Σ i, γ i)`.

## TODO

`Finset.sigmaLift` can be generalized to any alternative functor. But to make the generalization
worth it, we must first refactor the functor library so that the `alternative` instance for `Finset`
is computable and universe-polymorphic.
-/

open Function Multiset

variable {ι : Type*}

namespace Finset

section Sigma

variable {α : ι → Type*} {β : Type*} (s s₁ s₂ : Finset ι) (t t₁ t₂ : ∀ i, Finset (α i))

protected def sigma : Finset (Σ i, α i) :=
  ⟨_, s.nodup.sigma fun i => (t i).nodup⟩

variable {s s₁ s₂ t t₁ t₂}
