/-
Extracted from Algebra/Homology/SpectralObject/EpiMono.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Induced morphisms that are epi or mono

Given a spectral object in an abelian category, we show that certain
morphisms `E^n(f₁, f₂, f₃) ⟶ E^n(f₁', f₂', f₃')` are monomorphisms,
epimorphisms or isomorphisms.

## References
* [Jean-Louis Verdier, *Des catégories dérivées des catégories abéliennes*, II.4][verdier1996]

-/

namespace CategoryTheory

open Category Limits ComposableArrows

namespace Abelian

namespace SpectralObject

variable {C ι ι' κ : Type*} [Category* C] [Abelian C] [Category* ι] [Preorder ι']
  (X : SpectralObject C ι) (X' : SpectralObject C ι')

variable
  {i₀' i₀ i₁ i₂ i₃ i₃' : ι} (f₁ : i₀ ⟶ i₁)
  (f₁' : i₀' ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃) (f₃' : i₂ ⟶ i₃')
  (n₀ n₁ n₂ n₃ : ℤ)

lemma epi_map (α : mk₃ f₁ f₂ f₃ ⟶ mk₃ f₁ f₂ f₃') (n₀ n₁ n₂ n₃ : ℤ)
    (hα₀ : α.app 0 = 𝟙 _ := by cat_disch) (hα₁ : α.app 1 = 𝟙 _ := by cat_disch)
    (hα₂ : α.app 2 = 𝟙 _ := by cat_disch)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) (hn₃ : n₂ + 1 = n₃ := by lia) :
    Epi (X.map f₁ f₂ f₃ f₁ f₂ f₃' α n₀ n₁ n₂ hn₁ hn₂) :=
  have : Epi (X.cyclesMap f₁ f₂ f₁ f₂ (𝟙 (mk₂ f₁ f₂)) n₁) := by rw [X.cyclesMap_id]; infer_instance
  epi_of_epi_fac (X.πE_map _ _ _ _ _ _ α (𝟙 _) n₀ n₁ n₂ (by cat_disch) _ _)

lemma mono_map (α : mk₃ f₁ f₂ f₃ ⟶ mk₃ f₁' f₂ f₃) (n₀ n₁ n₂ n₃ : ℤ)
    (hα₁ : α.app 1 = 𝟙 _ := by cat_disch) (hα₂ : α.app 2 = 𝟙 _ := by cat_disch)
    (hα₃ : α.app 3 = 𝟙 _ := by cat_disch) (hn₁ : n₀ + 1 = n₁ := by lia)
    (hn₂ : n₁ + 1 = n₂ := by lia) (hn₃ : n₂ + 1 = n₃ := by lia) :
    Mono (X.map f₁ f₂ f₃ f₁' f₂ f₃ α n₀ n₁ n₂ hn₁ hn₂) := by
  have := X.map_ιE _ _ _ _ _ _ α (𝟙 _) n₀ n₁ n₂
  rw [opcyclesMap_id, comp_id] at this
  exact mono_of_mono_fac this

end

variable {i₀ i₁ i₂ i₃ i₄ i₅ i₆ i₇ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
  (f₄ : i₃ ⟶ i₄) (f₅ : i₄ ⟶ i₅)
  (f₂₃ : i₁ ⟶ i₃) (h₂₃ : f₂ ≫ f₃ = f₂₃)
  (f₃₄ : i₂ ⟶ i₄) (h₃₄ : f₃ ≫ f₄ = f₃₄)
  (n₀ n₁ n₂ n₃ : ℤ)
