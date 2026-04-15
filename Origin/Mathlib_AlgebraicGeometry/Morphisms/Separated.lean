/-
Extracted from AlgebraicGeometry/Morphisms/Separated.lean
Genuine: 15 | Conflates: 0 | Dissolved: 0 | Infrastructure: 18
-/
import Origin.Core
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Equalizer

/-!

# Separated morphisms

A morphism of schemes is separated if its diagonal morphism is a closed immmersion.

## Main definitions
- `AlgebraicGeometry.IsSeparated`: The class of separated morphisms.
- `AlgebraicGeometry.Scheme.IsSeparated`: The class of separated schemes.
- `AlgebraicGeometry.IsSeparated.hasAffineProperty`:
  A morphism is separated iff the preimage of affine opens are separated schemes.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

open scoped AlgebraicGeometry

namespace AlgebraicGeometry

variable {W X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

@[mk_iff]
class IsSeparated : Prop where
  /-- A morphism is separated if the diagonal map is a closed immersion. -/
  diagonal_isClosedImmersion : IsClosedImmersion (pullback.diagonal f) := by infer_instance

namespace IsSeparated

attribute [instance] diagonal_isClosedImmersion

theorem isSeparated_eq_diagonal_isClosedImmersion :
    @IsSeparated = MorphismProperty.diagonal @IsClosedImmersion := by
  ext
  exact isSeparated_iff _

instance (priority := 900) isSeparated_of_mono [Mono f] : IsSeparated f where

instance : MorphismProperty.RespectsIso @IsSeparated := by
  rw [isSeparated_eq_diagonal_isClosedImmersion]
  infer_instance

instance (priority := 900) [IsSeparated f] : QuasiSeparated f where

instance stableUnderComposition : MorphismProperty.IsStableUnderComposition @IsSeparated := by
  rw [isSeparated_eq_diagonal_isClosedImmersion]
  infer_instance

instance [IsSeparated f] [IsSeparated g] : IsSeparated (f ≫ g) :=
  stableUnderComposition.comp_mem f g inferInstance inferInstance

instance : MorphismProperty.IsMultiplicative @IsSeparated where
  id_mem _ := inferInstance

instance isStableUnderBaseChange : MorphismProperty.IsStableUnderBaseChange @IsSeparated := by
  rw [isSeparated_eq_diagonal_isClosedImmersion]
  infer_instance

instance : IsLocalAtTarget @IsSeparated := by
  rw [isSeparated_eq_diagonal_isClosedImmersion]
  infer_instance

instance (R S : CommRingCat.{u}) (f : R ⟶ S) : IsSeparated (Spec.map f) := by
  constructor
  letI := f.toAlgebra
  show IsClosedImmersion (Limits.pullback.diagonal (Spec.map (CommRingCat.ofHom (algebraMap R S))))
  rw [diagonal_Spec_map, MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion]
  exact .spec_of_surjective _ fun x ↦ ⟨.tmul R 1 x,
    (Algebra.TensorProduct.lmul'_apply_tmul (R := R) (S := S) 1 x).trans (one_mul x)⟩

@[instance 100]

lemma of_isAffineHom [h : IsAffineHom f] : IsSeparated f := by
  wlog hY : IsAffine Y
  · rw [IsLocalAtTarget.iff_of_iSup_eq_top (P := @IsSeparated) _
      (iSup_affineOpens_eq_top Y)]
    intro U
    have H : IsAffineHom (f ∣_ U) := IsLocalAtTarget.restrict h U
    exact this _ U.2
  have : IsAffine X := HasAffineProperty.iff_of_isAffine.mp h
  rw [MorphismProperty.arrow_mk_iso_iff @IsSeparated (arrowIsoSpecΓOfIsAffine f)]
  infer_instance

instance {S T : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (i : S ⟶ T) [IsSeparated i] :
    IsClosedImmersion (pullback.mapDesc f g i) :=
  MorphismProperty.of_isPullback (pullback_map_diagonal_isPullback f g i)
    inferInstance

instance [IsSeparated g] :
    IsClosedImmersion (pullback.lift (𝟙 _) f (Category.id_comp (f ≫ g))) := by
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion (pullback.fst f (𝟙 Y))]
  rw [← MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion _
    (pullback.congrHom rfl (Category.id_comp g)).inv]
  convert (inferInstanceAs <| IsClosedImmersion (pullback.mapDesc f (𝟙 _) g)) using 1
  ext : 1 <;> simp [pullback.condition]

end IsSeparated

section of_injective

open Scheme Pullback

variable (𝒰 : Y.OpenCover) (𝒱 : ∀ i, (pullback f (𝒰.map i)).OpenCover)

lemma Scheme.Pullback.diagonalCoverDiagonalRange_eq_top_of_injective
    (hf : Function.Injective f.base) :
    diagonalCoverDiagonalRange f 𝒰 𝒱 = ⊤ := by
  rw [← top_le_iff]
  rintro x -
  simp only [diagonalCoverDiagonalRange, openCoverOfBase_J, openCoverOfBase_obj,
    openCoverOfLeftRight_J, Opens.iSup_mk, Opens.carrier_eq_coe, Hom.opensRange_coe, Opens.coe_mk,
    Set.mem_iUnion, Set.mem_range, Sigma.exists]
  have H : (pullback.fst f f).base x = (pullback.snd f f).base x :=
    hf (by rw [← Scheme.comp_base_apply, ← Scheme.comp_base_apply, pullback.condition])
  let i := 𝒰.f (f.base ((pullback.fst f f).base x))
  obtain ⟨y : 𝒰.obj i, hy : (𝒰.map i).base y = f.base _⟩ :=
    𝒰.covers (f.base ((pullback.fst f f).base x))
  obtain ⟨z, hz₁, hz₂⟩ := exists_preimage_pullback _ _ hy.symm
  let j := (𝒱 i).f z
  obtain ⟨w : (𝒱 i).obj j, hy : ((𝒱 i).map j).base w = z⟩ := (𝒱 i).covers z
  refine ⟨i, j, ?_⟩
  simp_rw [diagonalCover_map]
  show x ∈ Set.range _
  dsimp only [diagonalCover, Cover.bind_obj, openCoverOfLeftRight_obj]
  rw [range_map]
  simp [← H, ← hz₁, ← hy]

lemma Scheme.Pullback.range_diagonal_subset_diagonalCoverDiagonalRange :
    Set.range (pullback.diagonal f).base ⊆ diagonalCoverDiagonalRange f 𝒰 𝒱 := by
  rintro _ ⟨x, rfl⟩
  simp only [diagonalCoverDiagonalRange, openCoverOfBase_J, openCoverOfBase_obj,
    openCoverOfLeftRight_J, Opens.iSup_mk, Opens.carrier_eq_coe, Hom.opensRange_coe, Opens.coe_mk,
    Set.mem_iUnion, Set.mem_range, Sigma.exists]
  let i := 𝒰.f (f.base x)
  obtain ⟨y : 𝒰.obj i, hy : (𝒰.map i).base y = f.base x⟩ := 𝒰.covers (f.base x)
  obtain ⟨z, hz₁, hz₂⟩ := exists_preimage_pullback _ _ hy.symm
  let j := (𝒱 i).f z
  obtain ⟨w : (𝒱 i).obj j, hy : ((𝒱 i).map j).base w = z⟩ := (𝒱 i).covers z
  refine ⟨i, j, (pullback.diagonal ((𝒱 i).map j ≫ pullback.snd f (𝒰.map i))).base w, ?_⟩
  rw [← hz₁, ← hy, ← Scheme.comp_base_apply, ← Scheme.comp_base_apply]
  dsimp only [diagonalCover, Cover.pullbackHom, Cover.bind_obj, openCoverOfLeftRight_obj]
  rw [← Scheme.comp_base_apply]
  congr 4
  apply pullback.hom_ext <;> simp

lemma isClosedImmersion_diagonal_restrict_diagonalCoverDiagonalRange
    [∀ i, IsAffine (𝒰.obj i)] [∀ i j, IsAffine ((𝒱 i).obj j)] :
    IsClosedImmersion (pullback.diagonal f ∣_ diagonalCoverDiagonalRange f 𝒰 𝒱) := by
  let U : (Σ i, (𝒱 i).J) → (diagonalCoverDiagonalRange f 𝒰 𝒱).toScheme.Opens := fun i ↦
    (diagonalCoverDiagonalRange f 𝒰 𝒱).ι ⁻¹ᵁ ((diagonalCover f 𝒰 𝒱).map ⟨i.1, i.2, i.2⟩).opensRange
  have hU (i) : (diagonalCoverDiagonalRange f 𝒰 𝒱).ι ''ᵁ U i =
      ((diagonalCover f 𝒰 𝒱).map ⟨i.1, i.2, i.2⟩).opensRange := by
    rw [TopologicalSpace.Opens.functor_obj_map_obj, inf_eq_right, Hom.image_top_eq_opensRange,
      Opens.opensRange_ι]
    exact le_iSup (fun i : Σ i, (𝒱 i).J ↦ ((diagonalCover f 𝒰 𝒱).map ⟨i.1, i.2, i.2⟩).opensRange) i
  have hf : iSup U = ⊤ := (TopologicalSpace.Opens.map_iSup _ _).symm.trans
    (diagonalCoverDiagonalRange f 𝒰 𝒱).ι_preimage_self
  rw [IsLocalAtTarget.iff_of_iSup_eq_top (P := @IsClosedImmersion) _ hf]
  intro i
  rw [MorphismProperty.arrow_mk_iso_iff (P := @IsClosedImmersion) (morphismRestrictRestrict _ _ _),
    MorphismProperty.arrow_mk_iso_iff (P := @IsClosedImmersion) (morphismRestrictEq _ (hU i)),
    MorphismProperty.arrow_mk_iso_iff (P := @IsClosedImmersion) (diagonalRestrictIsoDiagonal ..)]
  infer_instance

@[stacks 0DVA]
lemma isSeparated_of_injective (hf : Function.Injective f.base) :
    IsSeparated f := by
  constructor
  let 𝒰 := Y.affineCover
  let 𝒱 (i) := (pullback f (𝒰.map i)).affineCover
  refine IsLocalAtTarget.of_iSup_eq_top (fun i : PUnit.{0} ↦ ⊤) (by simp) fun _ ↦ ?_
  rw [← diagonalCoverDiagonalRange_eq_top_of_injective f 𝒰 𝒱 hf]
  exact isClosedImmersion_diagonal_restrict_diagonalCoverDiagonalRange f 𝒰 𝒱

end of_injective

lemma IsClosedImmersion.of_comp [IsClosedImmersion (f ≫ g)] [IsSeparated g] :
    IsClosedImmersion f := by
  rw [← pullback.lift_snd (𝟙 _) f (Category.id_comp (f ≫ g))]
  have := MorphismProperty.pullback_snd (P := @IsClosedImmersion) (f ≫ g) g inferInstance
  infer_instance

lemma IsSeparated.of_comp [IsSeparated (f ≫ g)] : IsSeparated f := by
  have := IsSeparated.diagonal_isClosedImmersion (f := f ≫ g)
  rw [pullback.diagonal_comp] at this
  exact ⟨@IsClosedImmersion.of_comp _ _ _ _ _ this inferInstance⟩

lemma IsSeparated.comp_iff [IsSeparated g] : IsSeparated (f ≫ g) ↔ IsSeparated f :=
  ⟨fun _ ↦ .of_comp f g, fun _ ↦ inferInstance⟩

@[stacks 01KM]
instance isClosedImmersion_equalizer_ι_left {S : Scheme} {X Y : Over S} [IsSeparated Y.hom]
    (f g : X ⟶ Y) : IsClosedImmersion (equalizer.ι f g).left := by
  refine MorphismProperty.of_isPullback
    ((Limits.isPullback_equalizer_prod f g).map (Over.forget _)).flip ?_
  rw [← MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion _
    (Over.prodLeftIsoPullback Y Y).hom]
  convert (inferInstanceAs (IsClosedImmersion (pullback.diagonal Y.hom)))
  ext1 <;> simp [← Over.comp_left]

lemma ext_of_isDominant_of_isSeparated [IsReduced X] {f g : X ⟶ Y}
    (s : Y ⟶ Z) [IsSeparated s] (h : f ≫ s = g ≫ s)
    (ι : W ⟶ X) [IsDominant ι] (hU : ι ≫ f = ι ≫ g) : f = g := by
  let X' : Over Z := Over.mk (f ≫ s)
  let Y' : Over Z := Over.mk s
  let U' : Over Z := Over.mk (ι ≫ f ≫ s)
  let f' : X' ⟶ Y' := Over.homMk f
  let g' : X' ⟶ Y' := Over.homMk g
  let ι' : U' ⟶ X' := Over.homMk ι
  have : IsSeparated Y'.hom := ‹_›
  have : IsDominant (equalizer.ι f' g').left := by
    apply (config := { allowSynthFailures := true }) IsDominant.of_comp (equalizer.lift ι' ?_).left
    · rwa [← Over.comp_left, equalizer.lift_ι]
    · ext1; exact hU
  have : Surjective (equalizer.ι f' g').left :=
    surjective_of_isDominant_of_isClosed_range _ IsClosedImmersion.base_closed.2
  have := isIso_of_isClosedImmersion_of_surjective (Y := X) (equalizer.ι f' g').left
  rw [← cancel_epi (equalizer.ι f' g').left]
  exact congr($(equalizer.condition f' g').left)

variable (S) in

lemma ext_of_isDominant_of_isSeparated' [X.Over S] [Y.Over S] [IsReduced X] [IsSeparated (Y ↘ S)]
    {f g : X ⟶ Y} [f.IsOver S] [g.IsOver S] {W} (ι : W ⟶ X) [IsDominant ι]
    (hU : ι ≫ f = ι ≫ g) : f = g :=
  ext_of_isDominant_of_isSeparated (Y ↘ S) (by simp) ι hU

namespace Scheme

@[mk_iff]
protected class IsSeparated (X : Scheme.{u}) : Prop where
  isSeparated_terminal_from : IsSeparated (terminal.from X)

attribute [instance] IsSeparated.isSeparated_terminal_from

lemma isSeparated_iff_isClosedImmersion_prod_lift {X : Scheme.{u}} :
    X.IsSeparated ↔ IsClosedImmersion (prod.lift (𝟙 X) (𝟙 X)) := by
  rw [isSeparated_iff, AlgebraicGeometry.isSeparated_iff, iff_iff_eq,
    ← MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion _ (prodIsoPullback X X).hom]
  congr
  ext : 1 <;> simp

instance [X.IsSeparated] : IsClosedImmersion (prod.lift (𝟙 X) (𝟙 X)) := by
  rwa [← isSeparated_iff_isClosedImmersion_prod_lift]

instance (priority := 900) {X : Scheme.{u}} [IsAffine X] : X.IsSeparated := ⟨inferInstance⟩

instance (priority := 900) [X.IsSeparated] : IsSeparated f := by
  apply (config := { allowSynthFailures := true }) @IsSeparated.of_comp (g := terminal.from Y)
  rw [terminal.comp_from]
  infer_instance

instance (f g : X ⟶ Y) [Y.IsSeparated] : IsClosedImmersion (Limits.equalizer.ι f g) :=
  MorphismProperty.of_isPullback (isPullback_equalizer_prod f g).flip inferInstance

end Scheme

instance IsSeparated.hasAffineProperty :
    HasAffineProperty @IsSeparated fun X _ _ _ ↦ X.IsSeparated := by
  convert HasAffineProperty.of_isLocalAtTarget @IsSeparated with X Y f hY
  rw [Scheme.isSeparated_iff, ← terminal.comp_from f, IsSeparated.comp_iff]
  rfl

lemma ext_of_isDominant [IsReduced X] {f g : X ⟶ Y} [Y.IsSeparated]
    (ι : W ⟶ X) [IsDominant ι] (hU : ι ≫ f = ι ≫ g) : f = g :=
  ext_of_isDominant_of_isSeparated (Limits.terminal.from _) (Limits.terminal.hom_ext _ _) ι hU

end AlgebraicGeometry
