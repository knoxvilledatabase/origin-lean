/-
Extracted from AlgebraicGeometry/Morphisms/Constructors.lean
Genuine: 7 of 12 | Dissolved: 0 | Infrastructure: 5
-/
import Origin.Core

/-!

# Constructors for properties of morphisms between schemes

This file provides some constructors to obtain morphism properties of schemes from other morphism
properties:

- `AffineTargetMorphismProperty.diagonal` : Given an affine target morphism property `P`,
  `P.diagonal f` holds if `P (pullback.mapDesc f₁ f₂ f)` holds for two affine open
  immersions `f₁` and `f₂`.
- `AffineTargetMorphismProperty.of`: Given a morphism property `P` of schemes,
  this is the restriction of `P` to morphisms with affine target. If `P` is local at the
  target, we have `(toAffineTargetMorphismProperty P).targetAffineLocally = P`, see:
  `MorphismProperty.targetAffineLocally_toAffineTargetMorphismProperty_eq_of_isZariskiLocalAtTarget`
- `MorphismProperty.topologically`: Given a property `P` of maps of topological spaces,
  `(topologically P) f` holds if `P` holds for the underlying continuous map of `f`.
- `MorphismProperty.stalkwise`: Given a property `P` of ring homomorphisms,
  `(stalkwise P) f` holds if `P` holds for all stalk maps.

Also provides API for showing the standard locality and stability properties for these
types of properties.

-/

universe u v w

open TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace AlgebraicGeometry

section Diagonal

def AffineTargetMorphismProperty.diagonal (P : AffineTargetMorphismProperty) :
    AffineTargetMorphismProperty :=
  fun {X _} f _ =>
    ∀ ⦃U₁ U₂ : Scheme⦄ (f₁ : U₁ ⟶ X) (f₂ : U₂ ⟶ X) [IsAffine U₁] [IsAffine U₂] [IsOpenImmersion f₁]
      [IsOpenImmersion f₂], P (pullback.mapDesc f₁ f₂ f)

-- INSTANCE (free from Core): AffineTargetMorphismProperty.diagonal_respectsIso

set_option backward.isDefEq.respectTransparency false in

theorem HasAffineProperty.diagonal_of_openCover (P) {Q} [HasAffineProperty P Q]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (𝒰 : Scheme.OpenCover.{v} Y) [∀ i, IsAffine (𝒰.X i)]
    (𝒰' : ∀ i, Scheme.OpenCover.{w} (pullback f (𝒰.f i))) [∀ i j, IsAffine ((𝒰' i).X j)]
    (h𝒰' : ∀ i j k,
      Q (pullback.mapDesc ((𝒰' i).f j) ((𝒰' i).f k) (𝒰.pullbackHom f i))) :
    P.diagonal f := by
  letI := isLocal_affineProperty P
  let 𝒱 := (Scheme.Pullback.openCoverOfBase 𝒰 f f).bind fun i =>
    Scheme.Pullback.openCoverOfLeftRight.{u} (𝒰' i) (𝒰' i) (pullback.snd _ _) (pullback.snd _ _)
  have i1 : ∀ i, IsAffine (𝒱.X i) := fun i => by dsimp [𝒱]; infer_instance
  apply of_openCover 𝒱
  rintro ⟨i, j, k⟩
  dsimp [𝒱]
  convert (Q.cancel_left_of_respectsIso
    ((pullbackDiagonalMapIso _ _ ((𝒰' i).f j) ((𝒰' i).f k)).inv ≫
      pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) _ _) (pullback.snd _ _)).mp _ using 1
  · simp
  · ext1 <;> simp
  · simp only [Category.assoc, limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app,
      Category.comp_id]
    convert h𝒰' i j k
    ext1 <;> simp [Scheme.Cover.pullbackHom]

theorem HasAffineProperty.diagonal_of_openCover_diagonal
    (P) {Q} [HasAffineProperty P Q]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (𝒰 : Scheme.OpenCover Y) [∀ i, IsAffine (𝒰.X i)]
    (h𝒰 : ∀ i, Q.diagonal (𝒰.pullbackHom f i)) :
    P.diagonal f :=
  diagonal_of_openCover P f 𝒰 (fun _ ↦ Scheme.affineCover _)
    (fun _ _ _ ↦ h𝒰 _ _ _)

set_option backward.isDefEq.respectTransparency false in

theorem HasAffineProperty.diagonal_of_diagonal_of_isPullback
    (P) {Q} [HasAffineProperty P Q]
    {X Y U V : Scheme.{u}} {f : X ⟶ Y} {g : U ⟶ Y}
    [IsAffine U] [IsOpenImmersion g]
    {iV : V ⟶ X} {f' : V ⟶ U} (h : IsPullback iV f' f g) (H : P.diagonal f) :
    Q.diagonal f' := by
  letI := isLocal_affineProperty P
  rw [← Q.diagonal.cancel_left_of_respectsIso h.isoPullback.inv,
    h.isoPullback_inv_snd]
  rintro U V f₁ f₂ hU hV hf₁ hf₂
  rw [← Q.cancel_left_of_respectsIso (pullbackDiagonalMapIso f _ f₁ f₂).hom]
  convert HasAffineProperty.of_isPullback (P := P) (.of_hasPullback _ _) H
  · apply pullback.hom_ext <;> simp
  · infer_instance
  · infer_instance

theorem HasAffineProperty.diagonal_iff
    (P) {Q} [HasAffineProperty P Q] {X Y : Scheme.{u}} {f : X ⟶ Y} [IsAffine Y] :
    Q.diagonal f ↔ P.diagonal f := by
  letI := isLocal_affineProperty P
  refine ⟨fun hf ↦ ?_, diagonal_of_diagonal_of_isPullback P .of_id_fst⟩
  rw [← Q.diagonal.cancel_left_of_respectsIso
    (pullback.fst (f := f) (g := 𝟙 Y)), pullback.condition, Category.comp_id] at hf
  let 𝒰 := X.affineCover.pushforwardIso (inv (pullback.fst (f := f) (g := 𝟙 Y)))
  have (i : _) : IsAffine (𝒰.X i) := by dsimp [𝒰]; infer_instance
  exact HasAffineProperty.diagonal_of_openCover.{u, u, u} P f (Scheme.coverOfIsIso (𝟙 _))
    (fun _ ↦ 𝒰) (fun _ _ _ ↦ hf _ _)

set_option backward.isDefEq.respectTransparency false in

theorem AffineTargetMorphismProperty.diagonal_of_openCover_source
    {Q : AffineTargetMorphismProperty} [Q.IsLocal]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (𝒰 : Scheme.OpenCover.{v} X) [∀ i, IsAffine (𝒰.X i)]
    [IsAffine Y] (h𝒰 : ∀ i j, Q (pullback.mapDesc (𝒰.f i) (𝒰.f j) f)) :
    Q.diagonal f := by
  rw [HasAffineProperty.diagonal_iff (targetAffineLocally Q)]
  let 𝒱 := Scheme.Pullback.openCoverOfLeftRight.{u} 𝒰 𝒰 f f
  have i1 : ∀ i, IsAffine (𝒱.X i) := fun i => by dsimp [𝒱]; infer_instance
  refine HasAffineProperty.of_openCover (P := targetAffineLocally Q) 𝒱 fun i ↦ ?_
  dsimp [𝒱, Scheme.Cover.pullbackHom]
  have : IsPullback (pullback.fst _ _ ≫ 𝒰.f _) (pullback.mapDesc (𝒰.f i.1) (𝒰.f i.2) f)
      (pullback.diagonal f) (pullback.map _ _ _ _ (𝒰.f _) (𝒰.f _) (𝟙 Y) (by simp) (by simp)) :=
    .of_iso (pullback_fst_map_snd_isPullback f (𝟙 _) (𝒰.f i.1 ≫ pullback.lift (𝟙 _) f)
      (𝒰.f i.2 ≫ pullback.lift (𝟙 _) f)) (asIso (pullback.map _ _ _ _ (𝟙 _) (𝟙 _)
      (pullback.fst _ _) (by simp) (by simp))) (.refl _) (pullback.congrHom (by simp) (by simp))
      (.refl _) (by simp) (by cat_disch) (by simp) (by cat_disch)
  rw [← Q.cancel_left_of_respectsIso this.isoPullback.hom, IsPullback.isoPullback_hom_snd]
  exact h𝒰 _ _

-- INSTANCE (free from Core): HasAffineProperty.diagonal_affineProperty_isLocal

-- INSTANCE (free from Core): (P)

-- INSTANCE (free from Core): (P)

open MorphismProperty in

-- INSTANCE (free from Core): (P

end Diagonal

section Universally

theorem universally_isZariskiLocalAtTarget (P : MorphismProperty Scheme)
    (hP₂ : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Type u} (U : ι → Y.Opens)
      (_ : IsOpenCover U), (∀ i, P (f ∣_ U i)) → P f) : IsZariskiLocalAtTarget P.universally := by
  apply IsZariskiLocalAtTarget.mk'
  · exact fun {X Y} f U => P.universally.of_isPullback
      (isPullback_morphismRestrict f U).flip
  · intro X Y f ι U hU H X' Y' i₁ i₂ f' h
    apply hP₂ _ (fun i ↦ i₂ ⁻¹ᵁ U i)
    · simp only [IsOpenCover, ← top_le_iff] at hU ⊢
      rintro x -
      simpa using @hU (i₂ x) trivial
    · rintro i
      refine H _ ((X'.isoOfEq ?_).hom ≫ i₁ ∣_ _) (i₂ ∣_ _) _ ?_
      · exact congr($(h.1.1) ⁻¹ᵁ U i)
      · rw [← (isPullback_morphismRestrict f _).paste_vert_iff]
        · simp only [Category.assoc, morphismRestrict_ι, Scheme.isoOfEq_hom_ι_assoc]
          exact (isPullback_morphismRestrict f' (i₂ ⁻¹ᵁ U i)).paste_vert h
        · rw [← cancel_mono (Scheme.Opens.ι _)]
          simp [morphismRestrict_ι_assoc, h.1.1]
