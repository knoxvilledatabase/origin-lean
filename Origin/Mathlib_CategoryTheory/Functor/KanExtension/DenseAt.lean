/-
Extracted from CategoryTheory/Functor/KanExtension/DenseAt.lean
Genuine: 6 of 6 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Canonical colimits, or functors that are dense at an object

Given a functor `F : C ⥤ D` and `Y : D`, we say that `F` is dense at `Y` (`F.DenseAt Y`),
if `Y` identifies to the colimit of all `F.obj X` for `X : C`
and `f : F.obj X ⟶ Y`, i.e. `Y` identifies to the colimit of
the obvious functor `CostructuredArrow F Y ⥤ D`. In some references,
it is also said that `Y` is a canonical colimit relatively to `F`.
While `F.DenseAt Y` contains data, we also introduce the
corresponding property `isDenseAt F` of objects of `D`.

## TODO

* formalize dense subcategories
* show the presheaves of types are canonical colimits relatively
  to the Yoneda embedding

## References
* https://ncatlab.org/nlab/show/dense+functor

-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Limits

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  (F : C ⥤ D)

namespace Functor

abbrev DenseAt (Y : D) : Type max u₁ u₂ v₂ :=
  (Functor.LeftExtension.mk (𝟭 D) F.rightUnitor.inv).IsPointwiseLeftKanExtensionAt Y

def denseAtEquiv (Y : D) :
    F.DenseAt Y ≃ IsColimit ((LeftExtension.mk (𝟭 D) F.rightUnitor.inv).coconeAt Y) :=
  .refl _

variable {F} {Y : D} (hY : F.DenseAt Y)

def DenseAt.ofIso {Y' : D} (e : Y ≅ Y') : F.DenseAt Y' :=
  LeftExtension.isPointwiseLeftKanExtensionAtOfIso' _ hY e

def DenseAt.ofNatIso {G : C ⥤ D} (e : F ≅ G) : G.DenseAt Y :=
  (IsColimit.equivOfNatIsoOfIso
      ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerLeft _ e) _ _
      (by exact Cocone.ext (Iso.refl _)))
    (hY.whiskerEquivalence (CostructuredArrow.mapNatIso e.symm))

noncomputable def DenseAt.precompEquivOfFinal
    {C' : Type*} [Category* C'] (G : C' ⥤ C) [(CostructuredArrow.pre G F Y).Final] :
    (G ⋙ F).DenseAt Y ≃ F.DenseAt Y :=
  Functor.Final.isColimitWhiskerEquiv (CostructuredArrow.pre G F Y)
    ((LeftExtension.mk (𝟭 D) F.rightUnitor.inv).coconeAt Y)

noncomputable def DenseAt.precompOfFinal
    {C' : Type*} [Category* C'] (G : C' ⥤ C) [(CostructuredArrow.pre G F Y).Final] :
    (G ⋙ F).DenseAt Y :=
  (DenseAt.precompEquivOfFinal G).symm hY
