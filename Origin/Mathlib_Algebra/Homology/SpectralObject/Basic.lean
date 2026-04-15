/-
Extracted from Algebra/Homology/SpectralObject/Basic.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Spectral objects in abelian categories

In this file, we introduce the category `SpectralObject C ι` of spectral
objects in an abelian category `C` indexed by the category `ι`.

## References
* [Jean-Louis Verdier, *Des catégories dérivées des catégories abéliennes*, II.4][verdier1996]

-/

namespace CategoryTheory

open Category Limits

namespace Abelian

variable (C ι : Type*) [Category C] [Category ι] [Abelian C]

open ComposableArrows

structure SpectralObject where
  /-- A sequence of functors from `ComposableArrows ι 1` to the abelian category.
  The image of `mk₁ f` will be referred to as `H^n(f)` in the documentation. -/
  H (n : ℤ) : ComposableArrows ι 1 ⥤ C
  /-- The connecting homomorphism of the spectral object. (Use `δ` instead.) -/
  δ' (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    functorArrows ι 1 2 2 ⋙ H n₀ ⟶ functorArrows ι 0 1 2 ⋙ H n₁
  exact₁' (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (D : ComposableArrows ι 2) :
    (mk₂ ((δ' n₀ n₁ h).app D) ((H n₁).map ((mapFunctorArrows ι 0 1 0 2 2).app D))).Exact
  exact₂' (n : ℤ) (D : ComposableArrows ι 2) :
    (mk₂ ((H n).map ((mapFunctorArrows ι 0 1 0 2 2).app D))
      ((H n).map ((mapFunctorArrows ι 0 2 1 2 2).app D))).Exact
  exact₃' (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (D : ComposableArrows ι 2) :
    (mk₂ ((H n₀).map ((mapFunctorArrows ι 0 2 1 2 2).app D)) ((δ' n₀ n₁ h).app D)).Exact

namespace SpectralObject

variable {C ι} (X : SpectralObject C ι)

def δ {i j k : ι} (f : i ⟶ j) (g : j ⟶ k) (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁ := by lia) :
    (X.H n₀).obj (mk₁ g) ⟶ (X.H n₁).obj (mk₁ f) :=
  (X.δ' n₀ n₁ hn₁).app (mk₂ f g)
