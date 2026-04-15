/-
Extracted from Topology/Sheaves/SheafCondition/PairwiseIntersections.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Equivalent formulations of the sheaf condition

We give an equivalent formulation of the sheaf condition.

Given any indexed type `ι`, we define `overlap ι`,
a category with objects corresponding to
* individual open sets, `single i`, and
* intersections of pairs of open sets, `pair i j`,
  with morphisms from `pair i j` to both `single i` and `single j`.

Any open cover `U : ι → Opens X` provides a functor `diagram U : overlap ι ⥤ (Opens X)ᵒᵖ`.

There is a canonical cone over this functor, `cone U`, whose cone point is `isup U`,
and in fact this is a limit cone.

A presheaf `F : Presheaf C X` is a sheaf precisely if it preserves this limit.
We express this in two equivalent ways, as
* `isLimit (F.mapCone (cone U))`, or
* `preservesLimit (diagram U) F`

We show that this sheaf condition is equivalent to the `OpensLeCover` sheaf condition, and
thereby also equivalent to the default sheaf condition.
-/

assert_not_exists IsOrderedMonoid

noncomputable section

universe w

open TopologicalSpace TopCat Opposite CategoryTheory CategoryTheory.Limits

variable {C : Type*} [Category* C] {X : TopCat.{w}}

namespace TopCat.Presheaf

def IsSheafPairwiseIntersections (F : Presheaf C X) : Prop :=
  ∀ ⦃ι : Type w⦄ (U : ι → Opens X), Nonempty (IsLimit (F.mapCone (Pairwise.cocone U).op))

def IsSheafPreservesLimitPairwiseIntersections (F : Presheaf C X) : Prop :=
  ∀ ⦃ι : Type w⦄ (U : ι → Opens X), PreservesLimit (Pairwise.diagram U).op F

end

namespace SheafCondition

variable {ι : Type*} (U : ι → Opens X)

open CategoryTheory.Pairwise
