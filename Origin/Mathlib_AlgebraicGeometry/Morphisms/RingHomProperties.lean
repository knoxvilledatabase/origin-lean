/-
Extracted from AlgebraicGeometry/Morphisms/RingHomProperties.lean
Genuine: 15 of 15 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Properties of morphisms from properties of ring homs.

We provide the basic framework for talking about properties of morphisms that come from properties
of ring homs. For `P` a property of ring homs, we have two ways of defining a property of scheme
morphisms:

Let `f : X ⟶ Y`,
- `targetAffineLocally (affineAnd P)`: the preimage of an affine open `U = Spec A` is affine
  (`= Spec B`) and `A ⟶ B` satisfies `P`. (in `Mathlib/AlgebraicGeometry/Morphisms/AffineAnd.lean`)
- `affineLocally P`: For each pair of affine open `U = Spec A ⊆ X` and `V = Spec B ⊆ f ⁻¹' U`,
  the ring hom `A ⟶ B` satisfies `P`.

For these notions to be well defined, we require `P` be a sufficient local property. For the former,
`P` should be local on the source (`RingHom.RespectsIso P`, `RingHom.LocalizationPreserves P`,
`RingHom.OfLocalizationSpan`), and `targetAffineLocally (affine_and P)` will be local on
the target.

For the latter `P` should be local on the target (`RingHom.PropertyIsLocal P`), and
`affineLocally P` will be local on both the source and the target.
We also provide the following interface:

## `HasRingHomProperty`

`HasRingHomProperty P Q` is a type class asserting that `P` is local at the target and the source,
and for `f : Spec B ⟶ Spec A`, it is equivalent to the ring hom property `Q` on `Γ(f)`.

For `HasRingHomProperty P Q` and `f : X ⟶ Y`, we provide these API lemmas:
- `AlgebraicGeometry.HasRingHomProperty.iff_appLE`:
    `P f` if and only if `Q (f.appLE U V _)` for all affine `U : Opens Y` and `V : Opens X`.
- `AlgebraicGeometry.HasRingHomProperty.iff_of_source_openCover`:
    If `Y` is affine, `P f ↔ ∀ i, Q ((𝒰.map i ≫ f).appTop)` for an affine open cover `𝒰` of `X`.
- `AlgebraicGeometry.HasRingHomProperty.iff_of_isAffine`:
    If `X` and `Y` are affine, then `P f ↔ Q (f.appTop)`.
- `AlgebraicGeometry.HasRingHomProperty.Spec_iff`:
    `P (Spec.map φ) ↔ Q φ`
- `AlgebraicGeometry.HasRingHomProperty.iff_of_iSup_eq_top`:
    If `Y` is affine, `P f ↔ ∀ i, Q (f.appLE ⊤ (U i) _)` for a family `U` of affine opens of `X`.
- `AlgebraicGeometry.HasRingHomProperty.of_isOpenImmersion`:
    If `f` is an open immersion then `P f`.
- `AlgebraicGeometry.HasRingHomProperty.isStableUnderBaseChange`:
    If `Q` is stable under base change, then so is `P`.

We also provide the instances `P.IsMultiplicative`, `P.IsStableUnderComposition`,
`IsZariskiLocalAtTarget P`, `IsZariskiLocalAtSource P`.

-/

universe u

open CategoryTheory Opposite TopologicalSpace CategoryTheory.Limits AlgebraicGeometry

namespace RingHom

variable (P : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop)

set_option backward.isDefEq.respectTransparency false in

theorem IsStableUnderBaseChange.pullback_fst_appTop
    (hP : IsStableUnderBaseChange P) (hP' : RespectsIso P)
    {X Y S : Scheme} [IsAffine X] [IsAffine Y] [IsAffine S] (f : X ⟶ S) (g : Y ⟶ S)
    (H : P g.appTop.hom) : P (pullback.fst f g).appTop.hom := by
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11224): change `rw` to `erw`
  erw [← PreservesPullback.iso_inv_fst AffineScheme.forgetToScheme (AffineScheme.ofHom f)
      (AffineScheme.ofHom g)]
  rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, hP'.cancel_right_isIso,
    AffineScheme.forgetToScheme_map]
  have := congr_arg Quiver.Hom.unop
      (PreservesPullback.iso_hom_fst AffineScheme.Γ.rightOp (AffineScheme.ofHom f)
        (AffineScheme.ofHom g))
  simp only [AffineScheme.Γ, Functor.rightOp_obj, Functor.comp_obj, Functor.op_obj, unop_comp,
    AffineScheme.forgetToScheme_obj, Scheme.Γ_obj, Functor.rightOp_map, Functor.comp_map,
    Functor.op_map, Quiver.Hom.unop_op, AffineScheme.forgetToScheme_map, Scheme.Γ_map] at this
  rw [← this, CommRingCat.hom_comp, hP'.cancel_right_isIso, ← pushoutIsoUnopPullback_inl_hom,
    CommRingCat.hom_comp, hP'.cancel_right_isIso]
  exact hP.pushout_inl hP' _ _ H

end RingHom

namespace AlgebraicGeometry

section affineLocally

variable (P : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop)

def sourceAffineLocally : AffineTargetMorphismProperty := fun X _ f _ =>
  ∀ U : X.affineOpens, P (f.appLE ⊤ U le_top).hom

abbrev affineLocally : MorphismProperty Scheme.{u} :=
  targetAffineLocally (sourceAffineLocally P)

theorem sourceAffineLocally_respectsIso (h₁ : RingHom.RespectsIso P) :
    (sourceAffineLocally P).toProperty.RespectsIso := by
  apply AffineTargetMorphismProperty.respectsIso_mk
  · introv H U
    have : IsIso (e.hom.appLE (e.hom ''ᵁ U) U.1 (e.hom.preimage_image_eq _).ge) :=
      inferInstanceAs (IsIso (e.hom.app _ ≫
        X.presheaf.map (eqToHom (e.hom.preimage_image_eq _).symm).op))
    rw [← Scheme.Hom.appLE_comp_appLE _ _ ⊤ (e.hom ''ᵁ U) U.1 le_top (e.hom.preimage_image_eq _).ge,
      CommRingCat.hom_comp, h₁.cancel_right_isIso]
    exact H ⟨_, U.prop.image_of_isOpenImmersion e.hom⟩
  · introv H U
    rw [Scheme.Hom.comp_appLE, CommRingCat.hom_comp, h₁.cancel_left_isIso]
    exact H U

theorem affineLocally_respectsIso (h : RingHom.RespectsIso P) : (affineLocally P).RespectsIso :=
  letI := sourceAffineLocally_respectsIso P h
  inferInstance

open Scheme in

theorem sourceAffineLocally_morphismRestrict {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.Opens) (hU : IsAffineOpen U) :
    @sourceAffineLocally P _ _ (f ∣_ U) hU ↔
      ∀ (V : X.affineOpens) (e : V.1 ≤ f ⁻¹ᵁ U), P (f.appLE U V e).hom := by
  dsimp only [sourceAffineLocally]
  simp only [morphismRestrict_appLE]
  rw [(affineOpensRestrict (f ⁻¹ᵁ U)).forall_congr_left, Subtype.forall]
  refine forall₂_congr fun V h ↦ ?_
  have := (affineOpensRestrict (f ⁻¹ᵁ U)).apply_symm_apply ⟨V, h⟩
  exact f.appLE_congr _ (Opens.ι_image_top _) congr($(this).1.1) (fun f => P f.hom)

theorem affineLocally_iff_affineOpens_le {X Y : Scheme.{u}} (f : X ⟶ Y) :
    affineLocally.{u} P f ↔
      ∀ (U : Y.affineOpens) (V : X.affineOpens) (e : V.1 ≤ f ⁻¹ᵁ U.1), P (f.appLE U V e).hom :=
  forall_congr' fun U ↦ sourceAffineLocally_morphismRestrict P f U U.2

theorem affineLocally_iff_forall_isAffineOpen {X Y : Scheme.{u}} (f : X ⟶ Y) :
    affineLocally.{u} P f ↔
      ∀ {U : Y.Opens} (_ : IsAffineOpen U) {V : X.Opens} (_ : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U),
      P (f.appLE U V e).hom := by
  simp [affineLocally_iff_affineOpens_le, Scheme.affineOpens]

set_option backward.isDefEq.respectTransparency false in

theorem sourceAffineLocally_isLocal (h₁ : RingHom.RespectsIso P)
    (h₂ : RingHom.LocalizationAwayPreserves P) (h₃ : RingHom.OfLocalizationSpan P) :
    (sourceAffineLocally P).IsLocal := by
  constructor
  · exact sourceAffineLocally_respectsIso P h₁
  · intro X Y _ f r H
    rw [sourceAffineLocally_morphismRestrict]
    intro U hU
    have : X.basicOpen (f.appLE ⊤ U (by simp) r) = U := by
      simp only [Scheme.Hom.appLE, Opens.map_top, CommRingCat.comp_apply]
      rw [Scheme.basicOpen_res]
      simpa using hU
    rw [← f.appLE_congr (by simp [Scheme.Hom.appLE]) rfl this (fun f => P f.hom),
      IsAffineOpen.appLE_eq_away_map f (isAffineOpen_top Y) U.2 _ r]
    simp only [CommRingCat.hom_ofHom]
    apply +allowSynthFailures h₂
    exact H U
  · introv hs hs' U
    apply h₃ _ _ hs
    intro r
    simp_rw [sourceAffineLocally_morphismRestrict] at hs'
    have := hs' r ⟨X.basicOpen (f.appLE ⊤ U le_top r.1), U.2.basicOpen (f.appLE ⊤ U le_top r.1)⟩
      (by simp [Scheme.Hom.appLE])
    rwa [IsAffineOpen.appLE_eq_away_map f (isAffineOpen_top Y) U.2, CommRingCat.hom_ofHom,
      ← h₁.isLocalization_away_iff] at this

variable {P}

lemma affineLocally_le {Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}
    (hPQ : ∀ {R S : Type u} [CommRing R] [CommRing S] {f : R →+* S}, P f → Q f) :
    affineLocally P ≤ affineLocally Q :=
  fun _ _ _ hf U V ↦ hPQ (hf U V)

open RingHom

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

lemma exists_basicOpen_le_appLE_of_appLE_of_isAffine
    (hPa : StableUnderCompositionWithLocalizationAwayTarget P) (hPl : LocalizationAwayPreserves P)
    (x : X) (U₁ : Y.affineOpens) (U₂ : Y.affineOpens) (V₁ : X.affineOpens) (V₂ : X.affineOpens)
    (hx₁ : x ∈ V₁.1) (hx₂ : x ∈ V₂.1) (e₂ : V₂.1 ≤ f ⁻¹ᵁ U₂.1) (h₂ : P (f.appLE U₂ V₂ e₂).hom)
    (hfx₁ : f x ∈ U₁.1) :
    ∃ (r : Γ(Y, U₁)) (s : Γ(X, V₁)) (_ : x ∈ X.basicOpen s)
      (e : X.basicOpen s ≤ f ⁻¹ᵁ Y.basicOpen r),
        P (f.appLE (Y.basicOpen r) (X.basicOpen s) e).hom := by
  obtain ⟨r, r', hBrr', hBfx⟩ := exists_basicOpen_le_affine_inter U₁.2 U₂.2 (f x)
    ⟨hfx₁, e₂ hx₂⟩
  have ha : IsAffineOpen (X.basicOpen (f.appLE U₂ V₂ e₂ r')) := V₂.2.basicOpen _
  have hxa : x ∈ X.basicOpen (f.appLE U₂ V₂ e₂ r') := by
    simpa [Scheme.Hom.appLE, ← Scheme.preimage_basicOpen] using And.intro hx₂ (hBrr' ▸ hBfx)
  obtain ⟨s, s', hBss', hBx⟩ := exists_basicOpen_le_affine_inter V₁.2 ha x ⟨hx₁, hxa⟩
  haveI := V₂.2.isLocalization_basicOpen (f.appLE U₂ V₂ e₂ r')
  haveI := U₂.2.isLocalization_basicOpen r'
  haveI := ha.isLocalization_basicOpen s'
  have ers : X.basicOpen s ≤ f ⁻¹ᵁ Y.basicOpen r := by
    rw [hBss', hBrr']
    apply le_trans (X.basicOpen_le _)
    simp [Scheme.Hom.appLE]
  have heq : f.appLE (Y.basicOpen r') (X.basicOpen s') (hBrr' ▸ hBss' ▸ ers) =
      f.appLE (Y.basicOpen r') (X.basicOpen (f.appLE U₂ V₂ e₂ r')) (by simp [Scheme.Hom.appLE]) ≫
        CommRingCat.ofHom (algebraMap _ _) := by
    simp only [Scheme.Hom.appLE, homOfLE_leOfHom, Category.assoc]
    congr
    apply X.presheaf.map_comp
  refine ⟨r, s, hBx, ers, ?_⟩
  · rw [f.appLE_congr _ hBrr' hBss' (fun f => P f.hom), heq]
    apply hPa _ s' _
    rw [U₂.2.appLE_eq_away_map f V₂.2]
    exact hPl _ _ _ _ h₂

lemma exists_affineOpens_le_appLE_of_appLE
    (hPa : StableUnderCompositionWithLocalizationAwayTarget P) (hPl : LocalizationAwayPreserves P)
    (x : X) (U₁ : Y.Opens) (U₂ : Y.affineOpens) (V₁ : X.Opens) (V₂ : X.affineOpens)
    (hx₁ : x ∈ V₁) (hx₂ : x ∈ V₂.1) (e₂ : V₂.1 ≤ f ⁻¹ᵁ U₂.1) (h₂ : P (f.appLE U₂ V₂ e₂).hom)
    (hfx₁ : f x ∈ U₁.1) :
    ∃ (U' : Y.affineOpens) (V' : X.affineOpens) (_ : U'.1 ≤ U₁) (_ : V'.1 ≤ V₁) (_ : x ∈ V'.1)
      (e : V'.1 ≤ f ⁻¹ᵁ U'.1), P (f.appLE U' V' e).hom := by
  obtain ⟨r, hBr, hBfx⟩ := U₂.2.exists_basicOpen_le ⟨f x, hfx₁⟩ (e₂ hx₂)
  obtain ⟨s, hBs, hBx⟩ := V₂.2.exists_basicOpen_le ⟨x, hx₁⟩ hx₂
  obtain ⟨r', s', hBx', e', hf'⟩ := exists_basicOpen_le_appLE_of_appLE_of_isAffine hPa hPl x
    ⟨Y.basicOpen r, U₂.2.basicOpen _⟩ U₂ ⟨X.basicOpen s, V₂.2.basicOpen _⟩ V₂ hBx hx₂ e₂ h₂ hBfx
  exact ⟨⟨Y.basicOpen r', (U₂.2.basicOpen _).basicOpen _⟩,
    ⟨X.basicOpen s', (V₂.2.basicOpen _).basicOpen _⟩, le_trans (Y.basicOpen_le _) hBr,
    le_trans (X.basicOpen_le _) hBs, hBx', e', hf'⟩

end affineLocally

class HasRingHomProperty (P : MorphismProperty Scheme.{u})
    (Q : outParam (∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop)) : Prop where
  isLocal_ringHomProperty : RingHom.PropertyIsLocal Q
  eq_affineLocally' : P = affineLocally Q

namespace HasRingHomProperty

variable (P : MorphismProperty Scheme.{u}) {Q} [HasRingHomProperty P Q]

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

lemma copy {P' : MorphismProperty Scheme.{u}}
    {Q' : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}
    (e : P = P') (e' : ∀ {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S), Q f ↔ Q' f) :
    HasRingHomProperty P' Q' := by
  subst e
  have heq : @Q = @Q' := by
    ext R S _ _ f
    exact (e' f)
  rw [← heq]
  infer_instance

lemma eq_affineLocally : P = affineLocally Q := eq_affineLocally'
