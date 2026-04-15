/-
Extracted from Algebra/Homology/LeftResolution/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Left resolutions

Given a fully faithful functor `ι : C ⥤ A` to an abelian category,
we introduce a structure `Abelian.LeftResolution ι` which gives
a functor `F : A ⥤ C` and a natural epimorphism
`π.app X : ι.obj (F.obj X) ⟶ X` for all `X : A`.
This is used in order to construct a resolution functor
`LeftResolution.chainComplexFunctor : A ⥤ ChainComplex C ℕ`.

This shall be used in order to construct functorial flat resolutions.

-/

namespace CategoryTheory.Abelian

open Category Limits Preadditive ZeroObject

variable {A C : Type*} [Category* C] [Category* A] (ι : C ⥤ A)

structure LeftResolution where
  /-- a functor which sends `X : A` to an object `F.obj X` with an epimorphism
    `π.app X : ι.obj (F.obj X) ⟶ X` -/
  F : A ⥤ C
  /-- the natural epimorphism -/
  π : F ⋙ ι ⟶ 𝟭 A
  epi_π_app (X : A) : Epi (π.app X) := by infer_instance

namespace LeftResolution

attribute [instance] epi_π_app

variable {ι} (Λ : LeftResolution ι) (X Y Z : A) (f : X ⟶ Y) (g : Y ⟶ Z)
