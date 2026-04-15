/-
Extracted from AlgebraicTopology/SimplicialSet/KanComplex.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.AlgebraicTopology.SimplicialSet.Basic

/-!
# Kan complexes

In this file we give the definition of Kan complexes.
In `Mathlib/AlgebraicTopology/Quasicategory/Basic.lean`
we show that every Kan complex is a quasicategory.

## TODO

- Show that the singular simplicial set of a topological space is a Kan complex.
- Generalize the definition to higher universes.
  Since `Λ[n, i]` is an object of `SSet.{0}`,
  the current definition of a Kan complex `S`
  requires `S : SSet.{0}`.

-/

namespace SSet

open CategoryTheory Simplicial

class KanComplex (S : SSet) : Prop where
  hornFilling : ∀ ⦃n : ℕ⦄ ⦃i : Fin (n+1)⦄ (σ₀ : Λ[n, i] ⟶ S),
    ∃ σ : Δ[n] ⟶ S, σ₀ = hornInclusion n i ≫ σ

end SSet
