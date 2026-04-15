/-
Extracted from CategoryTheory/SmallObject/IsCardinalForSmallObjectArgument.lean
Genuine: 16 of 16 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Cardinals that are suitable for the small object argument

In this file, given a class of morphisms `I : MorphismProperty C` and
a regular cardinal `κ : Cardinal.{w}`, we define a typeclass
`IsCardinalForSmallObjectArgument I κ` which requires certain
smallness properties (`I` is `w`-small, `C` is locally `w`-small),
the existence of certain colimits (pushouts, coproducts of size `w`,
and the condition `HasIterationOfShape κ.ord.ToType C` about the
existence of colimits indexed by limit ordinal smaller than or equal
to `κ.ord`), and the technical assumption that if `A` is the
a morphism in `I`, then the functor `Hom(A, _)` should commute
with the filtering colimits corresponding to relative
`I`-cell complexes. (This last condition shall hold when `κ`
is the successor of an infinite cardinal `c` such that all these objects `A` are `c`-presentable,
see `Mathlib/CategoryTheory/Presentable/Basic.lean`.)

Given `I : MorphismProperty C`, we shall say that `I` permits
the small object argument if there exists `κ` such that
`IsCardinalForSmallObjectArgument I κ` holds. See the file
`Mathlib/CategoryTheory/SmallObject/Basic.lean` for the definition of this typeclass
`HasSmallObjectArgument` and an outline of the proof.

## Main results

Assuming `IsCardinalForSmallObjectArgument I κ`, any morphism `f : X ⟶ Y`
is factored as `ιObj I κ f ≫ πObj I κ f = f`. It is shown that `ιObj I κ f`
is a relative `I`-cell complex (see `SmallObject.relativeCellComplexιObj`)
and that `πObj I κ f` has the right lifting property with respect to `I`
(see `SmallObject.rlp_πObj`). This construction is obtained by
iterating to the power `κ.ord.ToType` the functor `Arrow C ⥤ Arrow C` defined
in the file `Mathlib/CategoryTheory/SmallObject/Construction.lean`.
This factorization is functorial in `f`
and gives the property `HasFunctorialFactorization I.rlp.llp I.rlp`.
Finally, the lemma `llp_rlp_of_isCardinalForSmallObjectArgument`
(and its primed version) shows that the morphisms in `I.rlp.llp` are exactly
the retracts of the transfinite compositions (of shape `κ.ord.ToType`) of
pushouts of coproducts of morphisms in `I`.

## References
- https://ncatlab.org/nlab/show/small+object+argument

-/

universe w v v' u u'

namespace CategoryTheory

open Category HomotopicalAlgebra Limits SmallObject

variable {C : Type u} [Category.{v} C] (I : MorphismProperty C)

namespace MorphismProperty

class IsCardinalForSmallObjectArgument (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [OrderBot κ.ord.ToType] : Prop where
  isSmall : IsSmall.{w} I := by infer_instance
  locallySmall : LocallySmall.{w} C := by infer_instance
  hasPushouts : HasPushouts C := by infer_instance
  hasCoproducts : HasCoproducts.{w} C := by infer_instance
  hasIterationOfShape : HasIterationOfShape κ.ord.ToType C := by infer_instance
  preservesColimit {A B X Y : C} (i : A ⟶ B) (_ : I i) (f : X ⟶ Y)
    (hf : RelativeCellComplex.{w} (fun (_ : κ.ord.ToType) ↦ I.homFamily) f) :
    PreservesColimit hf.F (coyoneda.obj (Opposite.op A))

end MorphismProperty

namespace SmallObject

open MorphismProperty

variable (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [I.IsCardinalForSmallObjectArgument κ]

include I κ

lemma isSmall : IsSmall.{w} I :=
  IsCardinalForSmallObjectArgument.isSmall κ

lemma locallySmall : LocallySmall.{w} C :=
  IsCardinalForSmallObjectArgument.locallySmall I κ

lemma hasIterationOfShape : HasIterationOfShape κ.ord.ToType C :=
  IsCardinalForSmallObjectArgument.hasIterationOfShape I

lemma hasPushouts : HasPushouts C :=
  IsCardinalForSmallObjectArgument.hasPushouts I κ

lemma hasCoproducts : HasCoproducts.{w} C :=
  IsCardinalForSmallObjectArgument.hasCoproducts I κ

lemma preservesColimit {A B X Y : C} (i : A ⟶ B) (hi : I i) (f : X ⟶ Y)
    (hf : RelativeCellComplex.{w} (fun (_ : κ.ord.ToType) ↦ I.homFamily) f) :
    PreservesColimit hf.F (coyoneda.obj (Opposite.op A)) :=
  IsCardinalForSmallObjectArgument.preservesColimit i hi f hf

lemma hasColimitsOfShape_discrete (X Y : C) (p : X ⟶ Y) :
    HasColimitsOfShape
      (Discrete (FunctorObjIndex I.homFamily p)) C := by
  haveI := locallySmall I κ
  haveI := isSmall I κ
  haveI := hasCoproducts I κ
  exact hasColimitsOfShape_of_equivalence
    (Discrete.equivalence (equivShrink.{w} _)).symm

noncomputable def succStruct : SuccStruct (Arrow C ⥤ Arrow C) :=
  haveI := hasColimitsOfShape_discrete I κ
  haveI := hasPushouts I κ
  SuccStruct.ofNatTrans (ε I.homFamily)

noncomputable def attachCellsOfSuccStructProp
    {F G : Arrow C ⥤ Arrow C} {φ : F ⟶ G}
    (h : (succStruct I κ).prop φ) (f : Arrow C) :
    AttachCells.{w} I.homFamily (φ.app f).left :=
  haveI := locallySmall I κ
  haveI := isSmall I κ
  haveI := hasColimitsOfShape_discrete I κ
  haveI := hasPushouts I κ
  AttachCells.ofArrowIso (attachCellsιFunctorObjOfSmall _ _)
    ((Functor.mapArrow ((evaluation _ _).obj f ⋙
      Arrow.leftFunc)).mapIso h.arrowIso.symm)

def propArrow : MorphismProperty (Arrow C) := fun _ _ f ↦
  (coproducts.{w} I).pushouts f.left ∧ (isomorphisms C) f.right

lemma succStruct_prop_le_propArrow :
    (succStruct I κ).prop ≤ (propArrow.{w} I).functorCategory (Arrow C) := by
  haveI := locallySmall I κ
  haveI := isSmall I κ
  haveI := hasColimitsOfShape_discrete I κ
  haveI := hasPushouts I κ
  intro _ _ _ ⟨F⟩ f
  constructor
  · nth_rw 1 [← I.ofHoms_homFamily]
    apply pushouts_mk _ (functorObj_isPushout I.homFamily (F.obj f).hom)
    exact coproducts_of_small _ _ (colimitsOfShape_colimMap _ (by rintro ⟨j⟩; constructor))
  · rw [MorphismProperty.isomorphisms.iff]
    dsimp [succStruct]
    infer_instance

noncomputable def iterationFunctor : κ.ord.ToType ⥤ Arrow C ⥤ Arrow C :=
  haveI := hasIterationOfShape I κ
  (succStruct I κ).iterationFunctor κ.ord.ToType

noncomputable def iteration : Arrow C ⥤ Arrow C :=
  haveI := hasIterationOfShape I κ
  (succStruct I κ).iteration κ.ord.ToType

noncomputable def ιIteration : 𝟭 _ ⟶ iteration I κ :=
  haveI := hasIterationOfShape I κ
  (succStruct I κ).ιIteration κ.ord.ToType

noncomputable def transfiniteCompositionOfShapeSuccStructPropιIteration :
    (succStruct I κ).prop.TransfiniteCompositionOfShape κ.ord.ToType (ιIteration I κ) :=
  haveI := hasIterationOfShape I κ
  (succStruct I κ).transfiniteCompositionOfShapeιIteration κ.ord.ToType
