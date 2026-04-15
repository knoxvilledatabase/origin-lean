/-
Extracted from Topology/Sheaves/SheafCondition/OpensLeCover.lean
Genuine: 5 of 6 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Another version of the sheaf condition.

Given a family of open sets `U : ι → Opens X` we can form the subcategory
`{ V : Opens X // ∃ i, V ≤ U i }`, which has `iSup U` as a cocone.

The sheaf condition on a presheaf `F` is equivalent to
`F` sending the opposite of this cocone to a limit cone in `C`, for every `U`.

This condition is particularly nice when checking the sheaf condition
because we don't need to do any case bashing
(depending on whether we're looking at single or double intersections,
or equivalently whether we're looking at the first or second object in an equalizer diagram).

## Main statement

`TopCat.Presheaf.isSheaf_iff_isSheafOpensLeCover`: for a presheaf on a topological space,
the sheaf condition in terms of Grothendieck topology is equivalent to the `OpensLeCover`
sheaf condition. This result will be used to further connect to other sheaf conditions on spaces,
like `pairwise_intersections` and `equalizer_products`.

## References
* This is the definition Lurie uses in [Spectral Algebraic Geometry][LurieSAG].
-/

universe w

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopologicalSpace.Opens Opposite

namespace TopCat

variable {C : Type*} [Category* C]

variable {X : TopCat.{w}} (F : Presheaf C X) {ι : Type*} (U : ι → Opens X)

namespace Presheaf

namespace SheafCondition

def OpensLeCover : Type w :=
  ObjectProperty.FullSubcategory fun V : Opens X ↦ ∃ i, V ≤ U i

deriving Category

-- INSTANCE (free from Core): [h

namespace OpensLeCover

variable {U}

def index (V : OpensLeCover U) : ι :=
  V.property.choose

def homToIndex (V : OpensLeCover U) : V.obj ⟶ U (index V) :=
  V.property.choose_spec.hom

end OpensLeCover

def opensLeCoverCocone : Cocone (ObjectProperty.ι _ : OpensLeCover U ⥤ Opens X) where
  pt := iSup U
  ι := { app := fun V : OpensLeCover U => V.homToIndex ≫ Opens.leSupr U _ }

end SheafCondition

open SheafCondition

def IsSheafOpensLeCover : Prop :=
  ∀ ⦃ι : Type w⦄ (U : ι → Opens X), Nonempty (IsLimit (F.mapCone (opensLeCoverCocone U).op))

variable {Y : Opens X}
