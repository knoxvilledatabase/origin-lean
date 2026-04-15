/-
Extracted from AlgebraicTopology/SimplicialSet/KanComplex.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Kan complexes

In this file, the abbreviation `KanComplex` is introduced for
fibrant objects in the category `SSet` which is equipped with
Kan fibrations.

In `Mathlib/AlgebraicTopology/Quasicategory/Basic.lean`
we show that every Kan complex is a quasicategory.

## TODO

- Show that the singular simplicial set of a topological space is a Kan complex.

-/

universe u

namespace SSet

open CategoryTheory Simplicial Limits

open modelCategoryQuillen in

abbrev KanComplex (S : SSet.{u}) : Prop := HomotopicalAlgebra.IsFibrant S

lemma KanComplex.hornFilling {S : SSet.{u}} [KanComplex S]
    {n : ℕ} {i : Fin (n + 2)} (σ₀ : (Λ[n + 1, i] : SSet) ⟶ S) :
    ∃ σ : Δ[n + 1] ⟶ S, σ₀ = Λ[n + 1, i].ι ≫ σ := by
  have sq' : CommSq σ₀ Λ[n + 1, i].ι (terminal.from S) (terminal.from _) := ⟨by simp⟩
  exact ⟨sq'.lift, by simp⟩

end SSet
