/-
Extracted from AlgebraicGeometry/Morphisms/Basic.lean
Genuine: 25 of 26 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Properties of morphisms between Schemes

We provide the basic framework for talking about properties of morphisms between Schemes.

A `MorphismProperty Scheme` is a predicate on morphisms between schemes. For properties local at
the target, its behaviour is entirely determined by its definition on morphisms into affine schemes,
which we call an `AffineTargetMorphismProperty`. In this file, we provide API lemmas for properties
local at the target, and special support for those properties whose `AffineTargetMorphismProperty`
takes on a simpler form. We also provide API lemmas for properties local at the source.
The main interfaces of the API are the typeclasses `IsZariskiLocalAtTarget`,
`IsZariskiLocalAtSource` and `HasAffineProperty`, which we describe in detail below.

## `IsZariskiLocalAtTarget`

- `AlgebraicGeometry.IsZariskiLocalAtTarget`: We say that `IsZariskiLocalAtTarget P` for
  `P : MorphismProperty Scheme` if
  1. `P` respects isomorphisms.
  2. `P` holds for `f ∣_ U` for an open cover `U` of `Y` if and only if `P` holds for `f`.

For a morphism property `P` local at the target and `f : X ⟶ Y`, we provide these API lemmas:

- `AlgebraicGeometry.IsZariskiLocalAtTarget.of_isPullback`:
    `P` is preserved under pullback along open immersions.
- `AlgebraicGeometry.IsZariskiLocalAtTarget.restrict`:
    `P f → P (f ∣_ U)` for an open `U` of `Y`.
- `AlgebraicGeometry.IsZariskiLocalAtTarget.iff_of_iSup_eq_top`:
    `P f ↔ ∀ i, P (f ∣_ U i)` for a family `U` of open sets covering `Y`.
- `AlgebraicGeometry.IsZariskiLocalAtTarget.iff_of_openCover`:
    `P f ↔ ∀ i, P (𝒰.pullbackHom f i)` for `𝒰 : Y.OpenCover`.

## `IsZariskiLocalAtSource`

- `AlgebraicGeometry.IsZariskiLocalAtSource`: We say that `IsZariskiLocalAtSource P` for
  `P : MorphismProperty Scheme` if
  1. `P` respects isomorphisms.
  2. `P` holds for `𝒰.f i ≫ f` for an open cover `𝒰` of `X` iff `P` holds for `f : X ⟶ Y`.

For a morphism property `P` local at the source and `f : X ⟶ Y`, we provide these API lemmas:

- `AlgebraicGeometry.IsZariskiLocalAtSource.comp`:
    `P` is preserved under composition with open immersions at the source.
- `AlgebraicGeometry.IsZariskiLocalAtSource.iff_of_iSup_eq_top`:
    `P f ↔ ∀ i, P ((U i).ι ≫ f)` for a family `U` of open sets covering `X`.
- `AlgebraicGeometry.IsZariskiLocalAtSource.iff_of_openCover`:
    `P f ↔ ∀ i, P (𝒰.f i ≫ f)` for `𝒰 : X.OpenCover`.
- `AlgebraicGeometry.IsZariskiLocalAtSource.of_isOpenImmersion`: If `P` contains identities then `P`
    holds for open immersions.

## `AffineTargetMorphismProperty`

- `AlgebraicGeometry.AffineTargetMorphismProperty`:
    The type of predicates on `f : X ⟶ Y` with `Y` affine.
- `AlgebraicGeometry.AffineTargetMorphismProperty.IsLocal`: We say that `P.IsLocal` if `P`
    satisfies the assumptions of the affine communication lemma
    (`AlgebraicGeometry.of_affine_open_cover`). That is,
    1. `P` respects isomorphisms.
    2. If `P` holds for `f : X ⟶ Y`, then `P` holds for `f ∣_ Y.basicOpen r` for any
      global section `r`.
    3. If `P` holds for `f ∣_ Y.basicOpen r` for all `r` in a spanning set of the global sections,
      then `P` holds for `f`.

## `HasAffineProperty`

- `AlgebraicGeometry.HasAffineProperty`:
  `HasAffineProperty P Q` is a type class asserting that `P` is local at the target,
  and over affine schemes, it is equivalent to `Q : AffineTargetMorphismProperty`.

For `HasAffineProperty P Q` and `f : X ⟶ Y`, we provide these API lemmas:

- `AlgebraicGeometry.HasAffineProperty.of_isPullback`:
    `P` is preserved under pullback along open immersions from affine schemes.
- `AlgebraicGeometry.HasAffineProperty.restrict`:
    `P f → Q (f ∣_ U)` for affine `U` of `Y`.
- `AlgebraicGeometry.HasAffineProperty.iff_of_iSup_eq_top`:
    `P f ↔ ∀ i, Q (f ∣_ U i)` for a family `U` of affine open sets covering `Y`.
- `AlgebraicGeometry.HasAffineProperty.iff_of_openCover`:
    `P f ↔ ∀ i, Q (𝒰.pullbackHom f i)` for affine open covers `𝒰` of `Y`.
- `AlgebraicGeometry.HasAffineProperty.isStableUnderBaseChange`:
    If `Q` is stable under affine base change, then `P` is stable under arbitrary base change.

## Implementation details

The properties `IsZariskiLocalAtTarget` and `IsZariskiLocalAtSource` are defined as abbreviations
for the respective local property of morphism properties defined generally for categories equipped
with a `Precoverage`.
-/

universe u v

open TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace AlgebraicGeometry

abbrev IsZariskiLocalAtTarget (P : MorphismProperty Scheme.{u}) :=
  P.IsLocalAtTarget Scheme.zariskiPrecoverage

namespace IsZariskiLocalAtTarget

protected lemma mk' {P : MorphismProperty Scheme} [P.RespectsIso]
    (restrict : ∀ {X Y : Scheme} (f : X ⟶ Y) (U : Y.Opens), P f → P (f ∣_ U))
    (of_sSup_eq_top :
      ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Type u} (U : ι → Y.Opens), iSup U = ⊤ →
        (∀ i, P (f ∣_ U i)) → P f) :
    IsZariskiLocalAtTarget P where
  pullbackSnd 𝒰 i hf := (P.arrow_mk_iso_iff (morphismRestrictOpensRange _ _)).mp (restrict _ _ hf)
  of_zeroHypercover {X Y f} 𝒰 h := by
    refine of_sSup_eq_top f _ (Scheme.OpenCover.iSup_opensRange 𝒰) ?_
    exact fun i ↦ (P.arrow_mk_iso_iff (morphismRestrictOpensRange f _)).mpr (h i)

variable {P : MorphismProperty Scheme.{u}} [IsZariskiLocalAtTarget P]
  {X Y : Scheme.{u}} {f : X ⟶ Y} (𝒰 : Y.OpenCover)

lemma of_isPullback {UX UY : Scheme.{u}} {iY : UY ⟶ Y} [IsOpenImmersion iY]
    {iX : UX ⟶ X} {f' : UX ⟶ UY} (h : IsPullback iX f' f iY) (H : P f) : P f' :=
  MorphismProperty.IsLocalAtTarget.of_isPullback (Y.affineCover.add iY) .none h H

theorem restrict (hf : P f) (U : Y.Opens) : P (f ∣_ U) :=
  of_isPullback (isPullback_morphismRestrict f U).flip hf

lemma of_iSup_eq_top {ι} (U : ι → Y.Opens) (hU : iSup U = ⊤)
    (H : ∀ i, P (f ∣_ U i)) : P f := by
  refine (P.iff_of_zeroHypercover_target
    (Y.openCoverOfIsOpenCover (s := Set.range U) Subtype.val (by ext; simp [← hU]))).mpr fun i ↦ ?_
  obtain ⟨_, i, rfl⟩ := i
  refine (P.arrow_mk_iso_iff (morphismRestrictOpensRange f _)).mp ?_
  change P (f ∣_ (U i).ι.opensRange)
  rw [Scheme.Opens.opensRange_ι]
  exact H i

theorem iff_of_iSup_eq_top {ι} (U : ι → Y.Opens) (hU : iSup U = ⊤) :
    P f ↔ ∀ i, P (f ∣_ U i) :=
  ⟨fun H _ ↦ restrict H _, of_iSup_eq_top U hU⟩

lemma of_openCover (H : ∀ i, P (𝒰.pullbackHom f i)) : P f := by
  apply of_iSup_eq_top (fun i ↦ (𝒰.f i).opensRange) 𝒰.iSup_opensRange
  exact fun i ↦ (P.arrow_mk_iso_iff (morphismRestrictOpensRange f _)).mpr (H i)

theorem iff_of_openCover (𝒰 : Y.OpenCover) :
    P f ↔ ∀ i, P (𝒰.pullbackHom f i) :=
  ⟨fun H _ ↦ of_isPullback (.of_hasPullback _ _) H, of_openCover _⟩

lemma of_range_subset_iSup [P.RespectsRight @IsOpenImmersion] {ι : Type*} (U : ι → Y.Opens)
    (H : Set.range f ⊆ (⨆ i, U i : Y.Opens)) (hf : ∀ i, P (f ∣_ U i)) : P f := by
  let g : X ⟶ (⨆ i, U i : Y.Opens) := IsOpenImmersion.lift (Scheme.Opens.ι _) f (by simpa using H)
  rw [← IsOpenImmersion.lift_fac (⨆ i, U i).ι f (by simpa using H)]
  apply MorphismProperty.RespectsRight.postcomp (Q := @IsOpenImmersion) _ inferInstance
  rw [iff_of_iSup_eq_top (P := P) (U := fun i : ι ↦ (⨆ i, U i).ι ⁻¹ᵁ U i)]
  · intro i
    have heq : g ⁻¹ᵁ (⨆ i, U i).ι ⁻¹ᵁ U i = f ⁻¹ᵁ U i := by
      change (g ≫ (⨆ i, U i).ι) ⁻¹ᵁ U i = _
      simp [g]
    let e : Arrow.mk (g ∣_ (⨆ i, U i).ι ⁻¹ᵁ U i) ≅ Arrow.mk (f ∣_ U i) :=
        Arrow.isoMk (X.isoOfEq heq) (Scheme.Opens.isoOfLE (le_iSup U i)) <| by
      simp [← CategoryTheory.cancel_mono (U i).ι, g]
    rw [P.arrow_mk_iso_iff e]
    exact hf i
  apply (⨆ i, U i).ι.image_injective
  dsimp
  rw [Scheme.Hom.image_iSup, Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι]
  simp [Scheme.Hom.image_preimage_eq_opensRange_inf, le_iSup U]

lemma of_forall_exists_morphismRestrict (H : ∀ x, ∃ U : Y.Opens, x ∈ U ∧ P (f ∣_ U)) : P f := by
  choose U hxU hU using H
  refine IsZariskiLocalAtTarget.of_iSup_eq_top U (top_le_iff.mp fun x _ ↦ ?_) hU
  simpa using ⟨x, hxU x⟩

lemma of_forall_source_exists_preimage
    [P.RespectsRight IsOpenImmersion] [P.HasOfPostcompProperty IsOpenImmersion]
    (f : X ⟶ Y) (hX : ∀ x, ∃ (U : Y.Opens), f x ∈ U ∧ P ((f ⁻¹ᵁ U).ι ≫ f)) :
    P f := by
  choose U h₁ h₂ using hX
  apply IsZariskiLocalAtTarget.of_range_subset_iSup U
  · rintro y ⟨x, rfl⟩
    simp only [Opens.coe_iSup, Set.mem_iUnion, SetLike.mem_coe]
    exact ⟨x, h₁ x⟩
  · intro x
    exact P.of_postcomp (f ∣_ U x) (U x).ι (inferInstance : IsOpenImmersion _) (by simp [h₂])

set_option backward.isDefEq.respectTransparency false in

lemma coprodMap {X Y X' Y' : Scheme.{u}} (f : X ⟶ X') (g : Y ⟶ Y') (hf : P f) (hg : P g) :
    P (coprod.map f g) := by
  refine IsZariskiLocalAtTarget.of_openCover (coprodOpenCover.{_, 0} _ _) ?_
  rintro (⟨⟨⟩⟩ | ⟨⟨⟩⟩)
  · rw [← MorphismProperty.cancel_left_of_respectsIso P
      (isPullback_inl_inl_coprodMap f g).flip.isoPullback.hom]
    convert hf
    simp [Scheme.Cover.pullbackHom, coprodOpenCover]
  · rw [← MorphismProperty.cancel_left_of_respectsIso P
      (isPullback_inr_inr_coprodMap f g).flip.isoPullback.hom]
    convert hg
    simp [Scheme.Cover.pullbackHom, coprodOpenCover]

end IsZariskiLocalAtTarget

abbrev IsZariskiLocalAtSource (P : MorphismProperty Scheme.{u}) :=
  P.IsLocalAtSource Scheme.zariskiPrecoverage

namespace IsZariskiLocalAtSource

protected lemma mk' {P : MorphismProperty Scheme} [P.RespectsIso]
    (restrict : ∀ {X Y : Scheme} (f : X ⟶ Y) (U : X.Opens), P f → P (U.ι ≫ f))
    (of_sSup_eq_top :
      ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Type u} (U : ι → X.Opens), iSup U = ⊤ →
        (∀ i, P ((U i).ι ≫ f)) → P f) :
    IsZariskiLocalAtSource P where
  comp 𝒰 i H := by
    rw [← IsOpenImmersion.isoOfRangeEq_hom_fac (𝒰.f i) (Scheme.Opens.ι _)
      (congr_arg Opens.carrier (𝒰.f i).opensRange.opensRange_ι.symm), Category.assoc,
      P.cancel_left_of_respectsIso]
    exact restrict _ _ H
  of_zeroHypercover {X Y} f 𝒰 h := by
    refine of_sSup_eq_top f _ (Scheme.OpenCover.iSup_opensRange 𝒰) fun i ↦ ?_
    rw [← IsOpenImmersion.isoOfRangeEq_inv_fac (𝒰.f i) (Scheme.Opens.ι _)
      (congr_arg Opens.carrier (𝒰.f i).opensRange.opensRange_ι.symm), Category.assoc,
      P.cancel_left_of_respectsIso]
    exact h _

variable {P : MorphismProperty Scheme.{u}} [IsZariskiLocalAtSource P]

variable {X Y : Scheme.{u}} {f : X ⟶ Y} (𝒰 : X.OpenCover)

lemma comp {UX : Scheme.{u}} (H : P f) (i : UX ⟶ X) [IsOpenImmersion i] :
    P (i ≫ f) :=
  (P.iff_of_zeroHypercover_source (X.affineCover.add i)).mp H .none

-- INSTANCE (free from Core): respectsLeft_isOpenImmersion

lemma of_iSup_eq_top {ι} (U : ι → X.Opens) (hU : iSup U = ⊤)
    (H : ∀ i, P ((U i).ι ≫ f)) : P f := by
  refine (P.iff_of_zeroHypercover_source
    (X.openCoverOfIsOpenCover (s := Set.range U) Subtype.val (by ext; simp [← hU]))).mpr fun i ↦ ?_
  obtain ⟨_, i, rfl⟩ := i
  exact H i

theorem iff_of_iSup_eq_top {ι} (U : ι → X.Opens) (hU : iSup U = ⊤) :
    P f ↔ ∀ i, P ((U i).ι ≫ f) :=
  ⟨fun H _ ↦ comp H _, of_iSup_eq_top U hU⟩

lemma of_openCover (H : ∀ i, P (𝒰.f i ≫ f)) : P f := by
  refine of_iSup_eq_top (fun i ↦ (𝒰.f i).opensRange) 𝒰.iSup_opensRange fun i ↦ ?_
  rw [← IsOpenImmersion.isoOfRangeEq_inv_fac (𝒰.f i) (Scheme.Opens.ι _)
    (congr_arg Opens.carrier (𝒰.f i).opensRange.opensRange_ι.symm), Category.assoc,
    P.cancel_left_of_respectsIso]
  exact H i

theorem iff_of_openCover :
    P f ↔ ∀ i, P (𝒰.f i ≫ f) :=
  ⟨fun H _ ↦ comp H _, of_openCover _⟩

variable (f) in

lemma of_isOpenImmersion [P.ContainsIdentities] [IsOpenImmersion f] : P f :=
  Category.comp_id f ▸ comp (P.id_mem Y) f

lemma isZariskiLocalAtTarget [P.IsMultiplicative]
    (hP : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsOpenImmersion g], P (f ≫ g) → P f) :
    IsZariskiLocalAtTarget P where
  pullbackSnd {X Y} f 𝒰 i hf := by
    apply hP _ (𝒰.f i)
    rw [← pullback.condition]
    exact IsZariskiLocalAtSource.comp hf _
  of_zeroHypercover {X Y} f 𝒰 h := by
    rw [P.iff_of_zeroHypercover_source (𝒰.pullback₁ f)]
    intro i
    rw [← Scheme.Cover.pullbackHom_map]
    exact P.comp_mem _ _ (h i) (of_isOpenImmersion _)

set_option backward.isDefEq.respectTransparency false in

lemma sigmaDesc {X : Scheme.{u}} {ι : Type v} [Small.{u} ι] {Y : ι → Scheme.{u}}
    {f : ∀ i, Y i ⟶ X} (hf : ∀ i, P (f i)) : P (Sigma.desc f) := by
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := P) (Scheme.IsLocallyDirected.openCover _)]
  exact fun i ↦ by simp [hf]

section IsZariskiLocalAtSourceAndTarget

lemma resLE [IsZariskiLocalAtTarget P] {U : Y.Opens} {V : X.Opens}
    (e : V ≤ f ⁻¹ᵁ U)
    (hf : P f) : P (f.resLE U V e) :=
  IsZariskiLocalAtSource.comp (IsZariskiLocalAtTarget.restrict hf U) _

lemma iff_exists_resLE [IsZariskiLocalAtTarget P]
    [P.RespectsRight @IsOpenImmersion] :
    P f ↔ ∀ x : X, ∃ (U : Y.Opens) (V : X.Opens) (_ : x ∈ V.1) (e : V ≤ f ⁻¹ᵁ U),
      P (f.resLE U V e) := by
  refine ⟨fun hf x ↦ ⟨⊤, ⊤, trivial, by simp, resLE _ hf⟩, fun hf ↦ ?_⟩
  choose U V hxU e hf using hf
  rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top (fun x : X ↦ V x) (P := P)]
  · intro x
    rw [← Scheme.Hom.resLE_comp_ι _ (e x)]
    exact MorphismProperty.RespectsRight.postcomp (Q := @IsOpenImmersion) _ inferInstance _ (hf x)
  · rw [eq_top_iff]
    rintro x -
    simp only [Opens.mem_iSup]
    use x, hxU x

end IsZariskiLocalAtSourceAndTarget

end IsZariskiLocalAtSource

def AffineTargetMorphismProperty :=
  ∀ ⦃X Y : Scheme⦄ (_ : X ⟶ Y) [IsAffine Y], Prop

namespace AffineTargetMorphismProperty
