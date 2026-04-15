/-
Extracted from CategoryTheory/Monoidal/Cartesian/Over.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# `CartesianMonoidalCategory` for `Over X`

We provide a `CartesianMonoidalCategory (Over X)` instance via pullbacks, and provide simp lemmas
for the induced `MonoidalCategory (Over X)` instance.

-/

public noncomputable section

namespace CategoryTheory.Over

open Functor Limits CartesianMonoidalCategory

variable {C : Type*} [Category* C] [HasPullbacks C]

abbrev cartesianMonoidalCategory (X : C) : CartesianMonoidalCategory (Over X) :=
  .ofChosenFiniteProducts
    ⟨asEmptyCone (Over.mk (𝟙 X)), IsTerminal.ofUniqueHom (fun Y ↦ Over.homMk Y.hom)
      fun Y m ↦ Over.OverMorphism.ext (by simpa using m.w)⟩
    fun Y Z ↦ ⟨pullbackConeEquivBinaryFan.functor.obj (pullback.cone Y.hom Z.hom),
    (pullback.isLimit _ _).pullbackConeEquivBinaryFanFunctor⟩

attribute [local instance] cartesianMonoidalCategory

abbrev braidedCategory (X : C) : BraidedCategory (Over X) :=
  .ofCartesianMonoidalCategory

attribute [local instance] braidedCategory

open MonoidalCategory

variable {X : C}
