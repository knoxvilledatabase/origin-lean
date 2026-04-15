/-
Extracted from Algebra/Homology/SpectralObject/Differentials.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Differentials of a spectral object

Let `X` be a spectral object in an abelian category `C` indexed by a category `ι`.
In this file, we construct the differentials `d : E^{n}(f₃, f₄, f₅) ⟶ E^{n+1}(f₁, f₂, f₃)`
that are attached to families of five composable morphisms `f₁`, `f₂`, `f₃`, `f₄`, `f₅`
in `ι`. We show that `d ≫ d = 0`. The homology of these differentials is computed in the
file `Mathlib/Algebra/Homology/SpectralObject/Homology.lean`.

## References
* [Jean-Louis Verdier, *Des catégories dérivées des catégories abéliennes*, II.4][verdier1996]

-/

namespace CategoryTheory

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]

open Category ComposableArrows Limits Preadditive

namespace Abelian

namespace SpectralObject

variable (X : SpectralObject C ι)

variable {i₀ i₁ i₂ i₃ i₄ i₅ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
  (f₄ : i₃ ⟶ i₄) (f₅ : i₄ ⟶ i₅) (f₁₂ : i₀ ⟶ i₂) (h₁₂ : f₁ ≫ f₂ = f₁₂)
  (f₂₃ : i₁ ⟶ i₃) (h₂₃ : f₂ ≫ f₃ = f₂₃)
  (f₃₄ : i₂ ⟶ i₄) (h₃₄ : f₃ ≫ f₄ = f₃₄)
  (f₄₅ : i₃ ⟶ i₅) (h₄₅ : f₄ ≫ f₅ = f₄₅)
  (n₀ n₁ n₂ n₃ : ℤ)

noncomputable def d
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) (hn₃ : n₂ + 1 = n₃ := by lia) :
    X.E f₃ f₄ f₅ n₀ n₁ n₂ hn₁ hn₂ ⟶ X.E f₁ f₂ f₃ n₁ n₂ n₃ hn₂ hn₃ :=
  X.descE f₃ f₄ f₅ _ rfl n₀ n₁ n₂ (X.δ (f₁ ≫ f₂) (f₃ ≫ f₄) n₁ n₂ hn₂ ≫
    X.toCycles f₁ f₂ _ rfl n₂ ≫ X.πE f₁ f₂ f₃ n₁ n₂ n₃ hn₂ hn₃) (by
      rw [X.δ_naturality_assoc (f₁ ≫ f₂) f₃ (f₁ ≫ f₂) (f₃ ≫ f₄)
        (𝟙 _) (twoδ₂Toδ₁ f₃ f₄ _ rfl) n₁ n₂ rfl hn₂, Functor.map_id, id_comp,
        δ_toCycles_assoc .., δToCycles_πE ..]) hn₁
          (by rw [δ_δ_assoc .., zero_comp])
