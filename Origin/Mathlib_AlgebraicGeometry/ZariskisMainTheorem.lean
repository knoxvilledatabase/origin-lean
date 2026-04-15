/-
Extracted from AlgebraicGeometry/ZariskisMainTheorem.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Zariski's Main Theorem

In this file we prove Grothendieck's reformulation of Zariski's main theorem, namely if
`f : X ⟶ Y` is separated and of finite type, then the map from the quasi-finite locus `U ⊆ X` of
`f` to the relative normalization `X'` of `Y` in `X` is an open immersion.

We then have the following corollaries
- `Scheme.Hom.isOpen_quasiFiniteAt` : If `f` is separated and of finite type, then the quasi-finite
  locus of `f` is open.
- If `f` is itself quasi-finite, then the map `f.toNormalization : X ⟶ X'` is an open immersion.
  This can be accessed via `inferInstance`.
- `IsFinite.of_isProper_of_locallyQuasiFinite`:
  If `f` is proper and quasi-finite, then the map `f.toNormalization : X ⟶ X'` is an isomorphism,
  which implies that `f` itself is finite.

-/

open CategoryTheory Limits

namespace AlgebraicGeometry

universe u

variable {X Y S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]

set_option backward.isDefEq.respectTransparency false in

open TensorProduct in

theorem exists_etale_isCompl_of_quasiFiniteAt [IsSeparated f]
    {x : X} {s : S} (h : f x = s) (hx : f.QuasiFiniteAt x) :
    ∃ (U : Scheme) (g : U ⟶ S), Etale g ∧ s ∈ Set.range g ∧
    ∃ (V W : (pullback f g).Opens) (v : V), IsCompl V W ∧ IsFinite (V.ι ≫ pullback.snd f g) ∧
      pullback.fst f g v.1 = x := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hUV : V ≤ f ⁻¹ᵁ U⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (f ⁻¹ᵁ U).2
  have : (f.appLE U V hUV).hom.FiniteType := f.finiteType_appLE hU hV hUV
  algebraize [(f.appLE U V hUV).hom]
  have : (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.LiesOver (hU.primeIdealOf ⟨f x, hxU⟩).asIdeal := by
    suffices hU.primeIdealOf ⟨f x, hxU⟩ = Spec.map (f.appLE U V hUV) (hV.primeIdealOf ⟨x, hxV⟩) from
      ⟨congr(($this).1)⟩
    apply hU.isoSpec.inv.homeomorph.injective
    apply Subtype.ext
    simp only [IsAffineOpen.primeIdealOf, Scheme.Hom.homeomorph_apply,
      ← Scheme.Hom.comp_apply, ← Scheme.Opens.ι_apply, IsAffineOpen.isoSpec_hom]
    simp
  have : Algebra.QuasiFiniteAt Γ(S, U) (hV.primeIdealOf ⟨x, hxV⟩).asIdeal :=
    hx.quasiFiniteAt hV hU hUV hxV
  obtain ⟨R, _, _, _, P, _, _, e, _, P', _, _, hP', heP', -, _, -⟩ :=
    Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq
    (hU.primeIdealOf ⟨f x, hxU⟩).asIdeal (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  have : (algebraMap R (Localization.Away e)).Finite := RingHom.finite_algebraMap.mpr ‹_›
  let φ : Γ(S, U) ⟶ .of R := CommRingCat.ofHom <| algebraMap Γ(S, U) R
  have hφ : φ.hom.Etale := RingHom.etale_algebraMap.mpr ‹_›
  have : Etale (Spec.map φ) := HasRingHomProperty.Spec_iff.mpr hφ
  let e₁ : Spec (.of (R ⊗ Γ(X, V))) ≅ pullback (Spec.map (f.appLE U V hUV)) (Spec.map φ) :=
    (pullbackSpecIso _ _ _).symm ≪≫ pullbackSymmetry _ _
  have he₁ : e₁.hom ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom) := by
    dsimp [e₁, RingHom.algebraMap_toAlgebra]
    rw [Category.assoc, pullbackSymmetry_hom_comp_fst]
    exact pullbackSpecIso_inv_snd ..
  let g : Spec (.of (R ⊗[Γ(S, U)] Γ(X, V))) ⟶ pullback f (Spec.map φ ≫ hU.fromSpec) :=
    e₁.hom ≫ pullback.map _ _ _ _ hV.fromSpec (𝟙 _) hU.fromSpec
      (IsAffineOpen.SpecMap_appLE_fromSpec ..) (by simp)
  let W₁ := g ''ᵁ PrimeSpectrum.basicOpen e
  have : IsFinite (W₁.ι ≫ pullback.snd f _) := by
    let ι : Spec (.of (Localization.Away e)) ⟶ pullback f (Spec.map φ ≫ hU.fromSpec) :=
      Spec.map (CommRingCat.ofHom <| algebraMap _ _) ≫ g
    have : ι.opensRange = W₁ := by
      simp only [Scheme.Hom.opensRange_comp, ι, W₁]
      congr 1
      exact TopologicalSpace.Opens.ext <| PrimeSpectrum.localization_away_comap_range _ _
    rw [← this, ← MorphismProperty.cancel_left_of_respectsIso @IsFinite
      (Scheme.Hom.isoOpensRange _).hom]
    have H : (pullbackSpecIso _ R _).inv ≫ pullback.fst _ (Spec.map (f.appLE U V hUV)) = _ :=
      pullbackSpecIso_inv_fst ..
    simpa [Scheme.Hom.isoOpensRange, ι, g, e₁, RingHom.algebraMap_toAlgebra, φ, H,
      ← Spec.map_comp, IsFinite.SpecMap_iff]
  have : IsFinite W₁.ι := .of_comp _ (pullback.snd f _)
  let W₂ : (pullback f (Spec.map φ ≫ hU.fromSpec)).Opens :=
    ⟨W₁ᶜ, by simpa using W₁.ι.isClosedMap.isClosed_range⟩
  refine ⟨Spec (.of R), Spec.map φ ≫ hU.fromSpec, inferInstance,
    ⟨⟨P, ‹_›⟩, ?_⟩, W₁, W₂, ⟨g ⟨P', ‹_›⟩, ?_⟩, ?_, ‹_›, ?_⟩
  · dsimp [Spec.map_apply]
    convert hU.fromSpec_primeIdealOf ⟨f x, hxU⟩
    · exact PrimeSpectrum.ext (Ideal.over_def _ _).symm
    · simp [h]
  · exact ⟨⟨P', ‹_›⟩, heP', rfl⟩
  · simp [isCompl_iff, disjoint_iff, codisjoint_iff, W₂, SetLike.ext'_iff]
  · trans hV.fromSpec ⟨P'.comap Algebra.TensorProduct.includeRight.toRingHom, inferInstance⟩
    · simp [← Scheme.Hom.comp_apply, -Scheme.Hom.comp_base, g, reassoc_of% he₁]; rfl
    convert hV.fromSpec_primeIdealOf ⟨x, hxV⟩

variable {X Y S : Scheme.{u}} (f : X ⟶ Y)

set_option backward.isDefEq.respectTransparency false in

lemma Scheme.Hom.exists_mem_and_isIso_morphismRestrict_toNormalization
    [LocallyOfFiniteType f] [IsSeparated f] [QuasiCompact f]
    (x : X) (hx : f.QuasiFiniteAt x) :
    ∃ V, f.toNormalization x ∈ V ∧ IsIso (f.toNormalization ∣_ V) := by
  obtain ⟨T, fT, _, ⟨u, hu⟩, V, W, v, hVW, _, hv₂⟩ := exists_etale_isCompl_of_quasiFiniteAt _ rfl hx
  obtain ⟨U, hU, _⟩ : ∃ U, (pullback.snd f fT).toNormalization v.1 ∈ U ∧
      IsIso ((pullback.snd f fT).toNormalization ∣_ U) := by
    have hVW' : (W : Set ↑(pullback f fT)) = (↑V)ᶜ :=
      eq_compl_iff_isCompl.mpr (hVW.map TopologicalSpace.Opens.frameHom).symm
    have : IsClosedImmersion V.ι := .of_isPreimmersion _ (by simp [eq_compl_comm.mp hVW', W.isOpen])
    have : IsClosedImmersion W.ι := .of_isPreimmersion _ (by simpa [hVW'] using V.2)
    obtain ⟨H⟩ := nonempty_isColimit_binaryCofanMk_of_isCompl V.ι W.ι (by simpa)
    let e : (pullback.snd f fT).normalization ≅ V ⨿ (W.ι ≫ pullback.snd f fT).normalization :=
      (Scheme.Hom.normalizationCoprodIso (pullback.snd f fT) H).symm ≪≫
        coprod.mapIso (asIso (V.ι ≫ pullback.snd f fT).toNormalization).symm (.refl _)
    let ι : V.toScheme ⟶ V ⨿ (W.ι ≫ pullback.snd f fT).normalization := coprod.inl
    refine ⟨e.hom ⁻¹ᵁ ι.opensRange, ⟨v, ?_⟩, ?_⟩
    · rw [← V.ι_apply, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
      congr 5
      rw [← Category.assoc, ← Iso.comp_inv_eq]
      simp [ι, e, Scheme.Hom.normalizationCoprodIso]
    rw [← isIso_comp_right_iff _ (e.hom ∣_ ι.opensRange),
      ← morphismRestrict_comp, ← isIso_comp_right_iff _ ι.isoOpensRange.inv]
    have Heq : (pullback.snd f fT).toNormalization ⁻¹ᵁ e.hom ⁻¹ᵁ Scheme.Hom.opensRange ι = V := by
      apply le_antisymm
      · rintro a ⟨b, hab⟩
        by_contra h
        lift a to W using hVW'.ge h
        replace hab : ι b = ((W.ι ≫ pullback.snd f fT).toNormalization ≫ coprod.inr) a := by
          have : W.ι ≫ (H.coconePointUniqueUpToIso (colimit.isColimit _)).hom = coprod.inr :=
            H.comp_coconePointUniqueUpToIso_hom _ ⟨.right⟩
          simp only [← W.ι_apply, ← Scheme.Hom.comp_apply, Category.assoc, e] at hab
          simpa [-Scheme.Hom.comp_base, Scheme.Hom.normalizationCoprodIso,
            reassoc_of% this] using hab
        exact Set.disjoint_iff_forall_ne.mp
          (isCompl_range_inl_inr V (W.ι ≫ pullback.snd f fT).normalization).1 ⟨_, rfl⟩ ⟨_, rfl⟩ hab
      · rw [← Scheme.Hom.inv_image, ← SetLike.coe_subset_coe]
        simpa [← Scheme.Hom.opensRange_comp, ι, e, Scheme.Hom.normalizationCoprodIso,
          Set.range_comp] using Set.subset_preimage_image _ _
    convert (inferInstance : IsIso (Scheme.isoOfEq _ Heq).hom)
    rw [Iso.comp_inv_eq, ← Iso.inv_comp_eq, ← cancel_mono (Scheme.Opens.ι _)]
    have : V.ι ≫ (H.coconePointUniqueUpToIso (colimit.isColimit _)).hom = coprod.inl :=
      H.comp_coconePointUniqueUpToIso_hom _ ⟨.left⟩
    simp [e, Scheme.Hom.isoOpensRange, Scheme.Hom.normalizationCoprodIso, reassoc_of% this, ι]
  let fTn : (pullback.snd f fT).normalization ⟶ f.normalization :=
    f.normalizationPullback fT ≫ pullback.fst _ _
  let U' : f.normalization.Opens := ⟨_, fTn.isOpenMap _ U.2⟩
  refine ⟨U', ⟨_, hU, by simp only [← hv₂, ← Scheme.Hom.comp_apply]; simp [fTn]⟩, ?_⟩
  let fTnU : U.toScheme ⟶ U' := fTn.resLE _ _ (Set.subset_preimage_image _ _)
  have : Surjective fTnU := ⟨fun ⟨x, a, ha, e⟩ ↦ ⟨⟨a, ha⟩, Subtype.ext <| by simpa [fTnU] using e⟩⟩
  have H : (pullback.snd f fT).toNormalization ⁻¹ᵁ U ≤
      pullback.fst f fT ⁻¹ᵁ f.toNormalization ⁻¹ᵁ U' := by
    refine fun x hx ↦ ⟨_, hx, ?_⟩
    simp only [← Scheme.Hom.comp_apply]
    congr 5
    simp [fTn]
  have : IsPullback ((pullback.snd f fT).toNormalization ∣_ U)
      ((pullback.fst f fT).resLE _ _ H) fTnU (f.toNormalization ∣_ U') := by
    refine .of_bot (t := isPullback_morphismRestrict ..) ?_ ?_
    · simp only [Scheme.Hom.resLE_comp_ι, fTnU]
      refine .paste_vert (isPullback_morphismRestrict ..) ?_
      have H : IsPullback (pullback.map _ _ _ _ f.toNormalization (𝟙 _) (𝟙 _) (by simp) (by simp))
          (pullback.fst f fT) (pullback.fst f.fromNormalization fT) f.toNormalization :=
        .of_right (t := .flip <| .of_hasPullback ..)
          (by simpa using (.flip <| .of_hasPullback ..)) (by cat_disch)
      exact .of_iso' H (.refl _) (asIso <| f.normalizationPullback fT) (.refl _) (.refl _)
        (by cat_disch) (by simp) (by simp [fTn]) (by simp)
    · simp [← cancel_mono U'.ι, fTnU, fTn]
  exact MorphismProperty.of_isPullback_of_descendsAlong (P := .isomorphisms _)
    (Q := @Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) this
    ⟨⟨‹_›, inferInstance⟩, inferInstance⟩ ‹_›
