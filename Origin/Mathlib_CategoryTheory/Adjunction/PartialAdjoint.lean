/-
Extracted from CategoryTheory/Adjunction/PartialAdjoint.lean
Genuine: 7 of 9 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Domain of definition of the partial left adjoint

Given a functor `F : D ⥤ C`, we define a functor
`F.partialLeftAdjoint : F.PartialLeftAdjointSource ⥤ D` which is
defined on the full subcategory of `C` consisting of those objects `X : C`
such that `F ⋙ coyoneda.obj (op X) : D ⥤ Type _` is corepresentable.
For `X : F.PartialLeftAdjointSource` and `Y : D`, we have a natural bijection
`(F.partialLeftAdjoint.obj X ⟶ Y) ≃ (X.obj ⟶ F.obj Y)`
that is similar to what we would expect for the image of the object `X`
by the left adjoint of `F`, if such an adjoint existed.

Indeed, if the predicate `F.leftAdjointObjIsDefined` which defines
the `F.PartialLeftAdjointSource` holds for all
objects `X : C`, then `F` has a left adjoint.

When colimits indexed by a category `J` exist in `D`, we show that
the predicate `F.leftAdjointObjIsDefined` is stable under colimits indexed by `J`.

## TODO
* consider dualizing the results to right adjoints

-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace Functor

open Category Opposite Limits

section partialLeftAdjoint

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : D ⥤ C)

def leftAdjointObjIsDefined : ObjectProperty C :=
  fun X ↦ IsCorepresentable (F ⋙ coyoneda.obj (op X))

variable {F} in

lemma leftAdjointObjIsDefined_of_adjunction {G : C ⥤ D} (adj : G ⊣ F) (X : C) :
    F.leftAdjointObjIsDefined X :=
  (adj.corepresentableBy X).isCorepresentable

abbrev PartialLeftAdjointSource := F.leftAdjointObjIsDefined.FullSubcategory

-- INSTANCE (free from Core): (X

noncomputable def partialLeftAdjointObj (X : F.PartialLeftAdjointSource) : D :=
  (F ⋙ coyoneda.obj (op X.obj)).coreprX

noncomputable def partialLeftAdjointHomEquiv {X : F.PartialLeftAdjointSource} {Y : D} :
    (F.partialLeftAdjointObj X ⟶ Y) ≃ (X.obj ⟶ F.obj Y) :=
  (F ⋙ coyoneda.obj (op X.obj)).corepresentableBy.homEquiv

lemma partialLeftAdjointHomEquiv_comp {X : F.PartialLeftAdjointSource} {Y Y' : D}
    (f : F.partialLeftAdjointObj X ⟶ Y) (g : Y ⟶ Y') :
    F.partialLeftAdjointHomEquiv (f ≫ g) =
      F.partialLeftAdjointHomEquiv f ≫ F.map g := by
  apply CorepresentableBy.homEquiv_comp

noncomputable def partialLeftAdjointMap {X Y : F.PartialLeftAdjointSource}
    (f : X ⟶ Y) : F.partialLeftAdjointObj X ⟶ F.partialLeftAdjointObj Y :=
    F.partialLeftAdjointHomEquiv.symm (f.hom ≫ F.partialLeftAdjointHomEquiv (𝟙 _))
