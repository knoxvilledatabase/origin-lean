/-
Extracted from CategoryTheory/Triangulated/SpectralObject.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Spectral objects in triangulated categories

In this file, we introduce the category `SpectralObject C ι` of spectral
objects in a pretriangulated category `C` indexed by the category `ι`.

## TODO (@joelriou)
* construct the spectral object indexed by `WithTop (WithBot ℤ)` consisting
  of all truncations of an object of a triangulated category equipped with a t-structure
* define a similar notion of spectral objects in abelian categories, show that
  by applying a homological functor `C ⥤ A` to a spectral object in the
  triangulated category `C`, we obtain a spectral object in the abelian category `A`
* construct the spectral sequence attached to a spectral object in an abelian category

## References
* [Jean-Louis Verdier, *Des catégories dérivées des catégories abéliennes*, II.4][verdier1996]

-/

namespace CategoryTheory

open Limits Pretriangulated ComposableArrows

variable (C ι : Type*) [Category* C] [Category* ι] [HasZeroObject C]
  [HasShift C ℤ] [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]
  {D : Type*} [Category* D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D]

namespace Triangulated

structure SpectralObject where
  /-- A functor from `ComposableArrows ι 1` to the pretriangulated category. -/
  ω₁ : ComposableArrows ι 1 ⥤ C
  /-- The connecting homomorphism of the spectral object. -/
  δ' : functorArrows ι 1 2 2 ⋙ ω₁ ⟶ functorArrows ι 0 1 2 ⋙ ω₁ ⋙ shiftFunctor C (1 : ℤ)
  distinguished' (D : ComposableArrows ι 2) :
    Triangle.mk (ω₁.map ((mapFunctorArrows ι 0 1 0 2 2).app D))
      (ω₁.map ((mapFunctorArrows ι 0 2 1 2 2).app D)) (δ'.app D) ∈ distTriang C

namespace SpectralObject

variable {C ι} (X : SpectralObject C ι)
