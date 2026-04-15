/-
Extracted from CategoryTheory/Extensive.lean
Genuine: 23 of 43 | Dissolved: 0 | Infrastructure: 20
-/
import Origin.Core

/-!

# Extensive categories

## Main definitions
- `CategoryTheory.FinitaryExtensive`: A category is (finitary) extensive if it has finite
  coproducts, and binary coproducts are van Kampen.

## Main Results
- `CategoryTheory.hasStrictInitialObjects_of_finitaryExtensive`: The initial object
  in extensive categories is strict.
- `CategoryTheory.FinitaryExtensive.mono_inr_of_isColimit`: Coproduct injections are monic in
  extensive categories.
- `CategoryTheory.BinaryCofan.isPullback_initial_to_of_isVanKampen`: In extensive categories,
  sums are disjoint, i.e. the pullback of `X ⟶ X ⨿ Y` and `Y ⟶ X ⨿ Y` is the initial object.
- `CategoryTheory.types.finitaryExtensive`: The category of types is extensive.
- `CategoryTheory.FinitaryExtensive_TopCat`:
  The category `Top` is extensive.
- `CategoryTheory.FinitaryExtensive_functor`: The category `C ⥤ D` is extensive if `D`
  has all pullbacks and is extensive.
- `CategoryTheory.FinitaryExtensive.isVanKampen_finiteCoproducts`: Finite coproducts in a
  finitary extensive category are van Kampen.

## References
- https://ncatlab.org/nlab/show/extensive+category
- [Carboni et al, Introduction to extensive and distributive categories][CARBONI1993145]

-/

open CategoryTheory.Limits Topology

namespace CategoryTheory

universe v' u' v u v'' u''

variable {J : Type v'} [Category.{u'} J] {C : Type u} [Category.{v} C]

variable {D : Type u''} [Category.{v''} D]

section Extensive

variable {X Y : C}

class HasPullbacksOfInclusions (C : Type u) [Category.{v} C] [HasBinaryCoproducts C] : Prop where
  [hasPullbackInl : ∀ {X Y Z : C} (f : Z ⟶ X ⨿ Y), HasPullback coprod.inl f]

attribute [instance] HasPullbacksOfInclusions.hasPullbackInl

class PreservesPullbacksOfInclusions {C : Type*} [Category* C] {D : Type*} [Category* D]
    (F : C ⥤ D) [HasBinaryCoproducts C] where
  [preservesPullbackInl : ∀ {X Y Z : C} (f : Z ⟶ X ⨿ Y), PreservesLimit (cospan coprod.inl f) F]

attribute [instance] PreservesPullbacksOfInclusions.preservesPullbackInl

class FinitaryPreExtensive (C : Type u) [Category.{v} C] : Prop where
  [hasFiniteCoproducts : HasFiniteCoproducts C]
  [hasPullbacksOfInclusions : HasPullbacksOfInclusions C]
  /-- In a finitary extensive category, all coproducts are van Kampen -/
  universal' : ∀ {X Y : C} (c : BinaryCofan X Y), IsColimit c → IsUniversalColimit c

attribute [instance] FinitaryPreExtensive.hasFiniteCoproducts

attribute [instance] FinitaryPreExtensive.hasPullbacksOfInclusions

class FinitaryExtensive (C : Type u) [Category.{v} C] : Prop where
  [hasFiniteCoproducts : HasFiniteCoproducts C]
  [hasPullbacksOfInclusions : HasPullbacksOfInclusions C]
  /-- In a finitary extensive category, all coproducts are van Kampen -/
  van_kampen' : ∀ {X Y : C} (c : BinaryCofan X Y), IsColimit c → IsVanKampenColimit c

attribute [instance] FinitaryExtensive.hasFiniteCoproducts

attribute [instance] FinitaryExtensive.hasPullbacksOfInclusions

theorem FinitaryExtensive.vanKampen [FinitaryExtensive C] {F : Discrete WalkingPair ⥤ C}
    (c : Cocone F) (hc : IsColimit c) : IsVanKampenColimit c := by
  let X := F.obj ⟨WalkingPair.left⟩
  let Y := F.obj ⟨WalkingPair.right⟩
  have : F = pair X Y := by
    apply Functor.hext
    · rintro ⟨⟨⟩⟩ <;> rfl
    · rintro ⟨⟨⟩⟩ ⟨j⟩ ⟨⟨rfl : _ = j⟩⟩ <;> simp [X, Y]
  clear_value X Y
  subst this
  exact FinitaryExtensive.van_kampen' c hc

namespace HasPullbacksOfInclusions

-- INSTANCE (free from Core): (priority

variable [HasBinaryCoproducts C] [HasPullbacksOfInclusions C] {X Y Z : C} (f : Z ⟶ X ⨿ Y)

-- INSTANCE (free from Core): preservesPullbackInl'

set_option backward.isDefEq.respectTransparency false in

-- INSTANCE (free from Core): hasPullbackInr'

-- INSTANCE (free from Core): hasPullbackInr

end HasPullbacksOfInclusions

namespace PreservesPullbacksOfInclusions

variable {D : Type*} [Category* D] [HasBinaryCoproducts C] (F : C ⥤ D)

noncomputable

-- INSTANCE (free from Core): (priority

variable [PreservesPullbacksOfInclusions F] {X Y Z : C} (f : Z ⟶ X ⨿ Y)

noncomputable

-- INSTANCE (free from Core): preservesPullbackInl'

set_option backward.isDefEq.respectTransparency false in

noncomputable

-- INSTANCE (free from Core): preservesPullbackInr'

noncomputable

-- INSTANCE (free from Core): preservesPullbackInr

end PreservesPullbacksOfInclusions

-- INSTANCE (free from Core): (priority

theorem FinitaryExtensive.mono_inr_of_isColimit [FinitaryExtensive C] {c : BinaryCofan X Y}
    (hc : IsColimit c) : Mono c.inr :=
  BinaryCofan.mono_inr_of_isVanKampen (FinitaryExtensive.vanKampen c hc)

theorem FinitaryExtensive.mono_inl_of_isColimit [FinitaryExtensive C] {c : BinaryCofan X Y}
    (hc : IsColimit c) : Mono c.inl :=
  FinitaryExtensive.mono_inr_of_isColimit (BinaryCofan.isColimitFlip hc)

-- INSTANCE (free from Core): (priority

theorem FinitaryExtensive.isPullback_initial_to_binaryCofan [FinitaryExtensive C]
    {c : BinaryCofan X Y} (hc : IsColimit c) :
    IsPullback (initial.to _) (initial.to _) c.inl c.inr :=
  BinaryCofan.isPullback_initial_to_of_isVanKampen (FinitaryExtensive.vanKampen c hc)

-- INSTANCE (free from Core): (priority

set_option backward.isDefEq.respectTransparency false in

theorem finitaryExtensive_iff_of_isTerminal (C : Type u) [Category.{v} C] [HasFiniteCoproducts C]
    [HasPullbacksOfInclusions C]
    (T : C) (HT : IsTerminal T) (c₀ : BinaryCofan T T) (hc₀ : IsColimit c₀) :
    FinitaryExtensive C ↔ IsVanKampenColimit c₀ := by
  refine ⟨fun H => H.van_kampen' c₀ hc₀, fun H => ?_⟩
  constructor
  simp_rw [BinaryCofan.isVanKampen_iff] at H ⊢
  intro X Y c hc X' Y' c' αX αY f hX hY
  obtain ⟨d, hd, hd'⟩ :=
    Limits.BinaryCofan.IsColimit.desc' hc (HT.from _ ≫ c₀.inl) (HT.from _ ≫ c₀.inr)
  rw [H c' (αX ≫ HT.from _) (αY ≫ HT.from _) (f ≫ d) (by rw [← reassoc_of% hX, hd, Category.assoc])
      (by rw [← reassoc_of% hY, hd', Category.assoc])]
  obtain ⟨hl, hr⟩ := (H c (HT.from _) (HT.from _) d hd.symm hd'.symm).mp ⟨hc⟩
  rw [hl.paste_vert_iff hX.symm, hr.paste_vert_iff hY.symm]

-- INSTANCE (free from Core): types.finitaryExtensive

section TopCat

noncomputable def finitaryExtensiveTopCatAux (Z : TopCat.{u})
    (f : Z ⟶ TopCat.of (PUnit.{u + 1} ⊕ PUnit.{u + 1})) :
    IsColimit (BinaryCofan.mk
      (TopCat.pullbackFst f (TopCat.binaryCofan (TopCat.of PUnit) (TopCat.of PUnit)).inl)
      (TopCat.pullbackFst f (TopCat.binaryCofan (TopCat.of PUnit) (TopCat.of PUnit)).inr)) := by
  have h₁ : Set.range (TopCat.pullbackFst f (TopCat.binaryCofan (.of PUnit) (.of PUnit)).inl) =
      f ⁻¹' Set.range Sum.inl := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩; exact ⟨PUnit.unit, x.2.symm⟩
    · rintro x ⟨⟨⟩, hx⟩; refine ⟨⟨⟨x, PUnit.unit⟩, hx.symm⟩, rfl⟩
  have h₂ : Set.range (TopCat.pullbackFst f (TopCat.binaryCofan (.of PUnit) (.of PUnit)).inr) =
      f ⁻¹' Set.range Sum.inr := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩; exact ⟨PUnit.unit, x.2.symm⟩
    · rintro x ⟨⟨⟩, hx⟩; refine ⟨⟨⟨x, PUnit.unit⟩, hx.symm⟩, rfl⟩
  refine ((TopCat.binaryCofan_isColimit_iff _).mpr ⟨?_, ?_, ?_⟩).some
  · refine ⟨(Homeomorph.prodPUnit Z).isEmbedding.comp .subtypeVal, ?_⟩
    convert f.hom.2.1 _ isOpen_range_inl
  · refine ⟨(Homeomorph.prodPUnit Z).isEmbedding.comp .subtypeVal, ?_⟩
    convert f.hom.2.1 _ isOpen_range_inr
  · convert Set.isCompl_range_inl_range_inr.preimage f

-- INSTANCE (free from Core): finitaryExtensive_TopCat

end TopCat

section Functor

theorem finitaryExtensive_of_reflective
    [HasFiniteCoproducts D] [HasPullbacksOfInclusions D] [FinitaryExtensive C]
    {Gl : C ⥤ D} {Gr : D ⥤ C} (adj : Gl ⊣ Gr) [Gr.Full] [Gr.Faithful]
    [∀ X Y (f : X ⟶ Gl.obj Y), HasPullback (Gr.map f) (adj.unit.app Y)]
    [∀ X Y (f : X ⟶ Gl.obj Y), PreservesLimit (cospan (Gr.map f) (adj.unit.app Y)) Gl]
    [PreservesPullbacksOfInclusions Gl] :
    FinitaryExtensive D := by
  have : PreservesColimitsOfSize Gl := adj.leftAdjoint_preservesColimits
  constructor
  intro X Y c hc
  apply (IsVanKampenColimit.precompose_isIso_iff
    (Functor.isoWhiskerLeft _ (asIso adj.counit) ≪≫ Functor.rightUnitor _).hom).mp
  have : ∀ (Z : C) (i : Discrete WalkingPair) (f : Z ⟶ (colimit.cocone (pair X Y ⋙ Gr)).pt),
        PreservesLimit (cospan f ((colimit.cocone (pair X Y ⋙ Gr)).ι.app i)) Gl := by
    have : pair X Y ⋙ Gr = pair (Gr.obj X) (Gr.obj Y) := by
      apply Functor.hext
      · rintro ⟨⟨⟩⟩ <;> rfl
      · rintro ⟨⟨⟩⟩ ⟨j⟩ ⟨⟨rfl : _ = j⟩⟩ <;> simp
    rw [this]
    rintro Z ⟨_ | _⟩ f <;> dsimp <;> infer_instance
  refine ((FinitaryExtensive.vanKampen _ (colimit.isColimit <| pair X Y ⋙ _)).map_reflective
    adj).of_iso (IsColimit.uniqueUpToIso ?_ ?_)
  · exact isColimitOfPreserves Gl (colimit.isColimit _)
  · exact (IsColimit.precomposeHomEquiv _ _).symm hc

-- INSTANCE (free from Core): finitaryExtensive_functor

-- INSTANCE (free from Core): {C}

-- INSTANCE (free from Core): {C}

set_option backward.isDefEq.respectTransparency false in

theorem finitaryExtensive_of_preserves_and_reflects (F : C ⥤ D) [FinitaryExtensive D]
    [HasFiniteCoproducts C] [HasPullbacksOfInclusions C]
    [PreservesPullbacksOfInclusions F]
    [ReflectsLimitsOfShape WalkingCospan F] [PreservesColimitsOfShape (Discrete WalkingPair) F]
    [ReflectsColimitsOfShape (Discrete WalkingPair) F] : FinitaryExtensive C := by
  constructor
  intro X Y c hc
  refine IsVanKampenColimit.of_iso ?_ (hc.uniqueUpToIso (coprodIsCoprod X Y)).symm
  have (i : Discrete WalkingPair) (Z : C) (f : Z ⟶ X ⨿ Y) :
    PreservesLimit (cospan f ((BinaryCofan.mk coprod.inl coprod.inr).ι.app i)) F := by
    rcases i with ⟨_ | _⟩ <;> dsimp <;> infer_instance
  refine (FinitaryExtensive.vanKampen _
    (isColimitOfPreserves F (coprodIsCoprod X Y))).of_mapCocone F

theorem finitaryExtensive_of_preserves_and_reflects_isomorphism (F : C ⥤ D) [FinitaryExtensive D]
    [HasFiniteCoproducts C] [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan F]
    [PreservesColimitsOfShape (Discrete WalkingPair) F] [F.ReflectsIsomorphisms] :
    FinitaryExtensive C := by
  haveI : ReflectsLimitsOfShape WalkingCospan F := reflectsLimitsOfShape_of_reflectsIsomorphisms
  haveI : ReflectsColimitsOfShape (Discrete WalkingPair) F :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  exact finitaryExtensive_of_preserves_and_reflects F

end Functor

section FiniteCoproducts

theorem FinitaryPreExtensive.isUniversal_finiteCoproducts_Fin [FinitaryPreExtensive C] {n : ℕ}
    {F : Discrete (Fin n) ⥤ C} {c : Cocone F} (hc : IsColimit c) : IsUniversalColimit c := by
  let f : Fin n → C := F.obj ∘ Discrete.mk
  have : F = Discrete.functor f :=
    Functor.hext (fun _ ↦ rfl) (by rintro ⟨i⟩ ⟨j⟩ ⟨⟨rfl : i = j⟩⟩; simp [f])
  clear_value f
  subst this
  induction n with
  | zero => exact (isVanKampenColimit_of_isEmpty _ hc).isUniversal
  | succ n IH =>
    refine IsUniversalColimit.of_iso (@isUniversalColimit_extendCofan _ _ _ _ _ _
      (IH _ (coproductIsCoproduct _)) (FinitaryPreExtensive.universal' _ (coprodIsCoprod _ _)) ?_)
      ((extendCofanIsColimit f (coproductIsCoproduct _) (coprodIsCoprod _ _)).uniqueUpToIso hc)
    · dsimp
      infer_instance

theorem FinitaryPreExtensive.isUniversal_finiteCoproducts [FinitaryPreExtensive C] {ι : Type*}
    [Finite ι] {F : Discrete ι ⥤ C} {c : Cocone F} (hc : IsColimit c) : IsUniversalColimit c := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  apply (IsUniversalColimit.whiskerEquivalence_iff (Discrete.equivalence e).symm).mp
  apply FinitaryPreExtensive.isUniversal_finiteCoproducts_Fin
  exact (IsColimit.whiskerEquivalenceEquiv (Discrete.equivalence e).symm) hc

theorem FinitaryExtensive.isVanKampen_finiteCoproducts_Fin [FinitaryExtensive C] {n : ℕ}
    {F : Discrete (Fin n) ⥤ C} {c : Cocone F} (hc : IsColimit c) : IsVanKampenColimit c := by
  let f : Fin n → C := F.obj ∘ Discrete.mk
  have : F = Discrete.functor f :=
    Functor.hext (fun _ ↦ rfl) (by rintro ⟨i⟩ ⟨j⟩ ⟨⟨rfl : i = j⟩⟩; simp [f])
  clear_value f
  subst this
  induction n with
  | zero => exact isVanKampenColimit_of_isEmpty _ hc
  | succ n IH =>
    apply IsVanKampenColimit.of_iso _
      ((extendCofanIsColimit f (coproductIsCoproduct _) (coprodIsCoprod _ _)).uniqueUpToIso hc)
    apply @isVanKampenColimit_extendCofan _ _ _ _ _ _ _ _ ?_
    · apply IH
      exact coproductIsCoproduct _
    · apply FinitaryExtensive.van_kampen'
      exact coprodIsCoprod _ _
    · dsimp
      infer_instance

theorem FinitaryExtensive.isVanKampen_finiteCoproducts [FinitaryExtensive C] {ι : Type*}
    [Finite ι] {F : Discrete ι ⥤ C} {c : Cocone F} (hc : IsColimit c) : IsVanKampenColimit c := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  apply (IsVanKampenColimit.whiskerEquivalence_iff (Discrete.equivalence e).symm).mp
  apply FinitaryExtensive.isVanKampen_finiteCoproducts_Fin
  exact (IsColimit.whiskerEquivalenceEquiv (Discrete.equivalence e).symm) hc

set_option backward.isDefEq.respectTransparency false in

lemma FinitaryPreExtensive.hasPullbacks_of_is_coproduct [FinitaryPreExtensive C] {ι : Type*}
    [Finite ι] {F : Discrete ι ⥤ C} {c : Cocone F} (hc : IsColimit c) (i : Discrete ι) {X : C}
    (g : X ⟶ _) : HasPullback g (c.ι.app i) := by
  classical
  let f : ι → C := F.obj ∘ Discrete.mk
  have : F = Discrete.functor f :=
    Functor.hext (fun i ↦ rfl) (by rintro ⟨i⟩ ⟨j⟩ ⟨⟨rfl : i = j⟩⟩; simp [f])
  clear_value f
  subst this
  change Cofan f at c
  obtain ⟨i⟩ := i
  let e : ∐ f ≅ f i ⨿ (∐ fun j : ({i}ᶜ : Set ι) ↦ f j) :=
  { hom := Sigma.desc (fun j ↦ if h : j = i then eqToHom (congr_arg f h) ≫ coprod.inl else
      Sigma.ι (fun j : ({i}ᶜ : Set ι) ↦ f j) ⟨j, h⟩ ≫ coprod.inr)
    inv := coprod.desc (Sigma.ι f i) (Sigma.desc fun j ↦ Sigma.ι f j)
    hom_inv_id := by cat_disch
    inv_hom_id := by
      ext j
      · simp
      · simp only [coprod.desc_comp, colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app,
          eqToHom_refl, Category.id_comp, dite_true, BinaryCofan.mk_pt, BinaryCofan.ι_app_right,
          BinaryCofan.mk_inr, colimit.ι_desc_assoc, Discrete.functor_obj, Category.comp_id]
        exact dif_neg j.prop }
  let e' : c.pt ≅ f i ⨿ (∐ fun j : ({i}ᶜ : Set ι) ↦ f j) :=
    hc.coconePointUniqueUpToIso (getColimitCocone _).2 ≪≫ e
  have : coprod.inl ≫ e'.inv = c.ι.app ⟨i⟩ := by
    simp only [e, e', Iso.trans_inv, coprod.desc_comp, colimit.ι_desc, BinaryCofan.mk_pt,
      BinaryCofan.ι_app_left, BinaryCofan.mk_inl]
    exact colimit.comp_coconePointUniqueUpToIso_inv _ _
  clear_value e'
  rw [← this]
  have : IsPullback (𝟙 _) (g ≫ e'.hom) g e'.inv := IsPullback.of_horiz_isIso ⟨by simp⟩
  exact ⟨⟨⟨_, ((IsPullback.of_hasPullback (g ≫ e'.hom) coprod.inl).paste_horiz this).isLimit⟩⟩⟩

lemma FinitaryExtensive.mono_ι [FinitaryExtensive C] {ι : Type*} [Finite ι] {F : Discrete ι ⥤ C}
    {c : Cocone F} (hc : IsColimit c) (i : Discrete ι) :
    Mono (c.ι.app i) :=
  mono_of_cofan_isVanKampen (isVanKampen_finiteCoproducts hc) _

-- INSTANCE (free from Core): [FinitaryExtensive

lemma FinitaryExtensive.isPullback_initial_to [FinitaryExtensive C]
    {ι : Type*} [Finite ι] {F : Discrete ι ⥤ C}
    {c : Cocone F} (hc : IsColimit c) (i j : Discrete ι) (e : i ≠ j) :
    IsPullback (initial.to _) (initial.to _) (c.ι.app i) (c.ι.app j) :=
  isPullback_initial_to_of_cofan_isVanKampen (isVanKampen_finiteCoproducts hc) i j e

lemma FinitaryExtensive.isPullback_initial_to_sigma_ι [FinitaryExtensive C] {ι : Type*} [Finite ι]
    (X : ι → C) (i j : ι) (e : i ≠ j) :
    IsPullback (initial.to _) (initial.to _) (Sigma.ι X i) (Sigma.ι X j) :=
  FinitaryExtensive.isPullback_initial_to (coproductIsCoproduct _) ⟨i⟩ ⟨j⟩
    (ne_of_apply_ne Discrete.as e)

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): FinitaryPreExtensive.hasPullbacks_of_inclusions

lemma FinitaryPreExtensive.isIso_sigmaDesc_fst [FinitaryPreExtensive C] {α : Type} [Finite α]
    {X : C} {Z : α → C} (π : (a : α) → Z a ⟶ X) {Y : C} (f : Y ⟶ X) (hπ : IsIso (Sigma.desc π)) :
    IsIso (Sigma.desc ((fun _ ↦ pullback.fst _ _) : (a : α) → pullback f (π a) ⟶ _)) := by
  let c := (Cofan.mk _ ((fun _ ↦ pullback.fst _ _) : (a : α) → pullback f (π a) ⟶ _))
  apply c.nonempty_isColimit_iff_isIso_sigmaDesc.mp
  have hau : IsUniversalColimit (Cofan.mk X π) := FinitaryPreExtensive.isUniversal_finiteCoproducts
    ((Cofan.nonempty_isColimit_iff_isIso_sigmaDesc _).mpr hπ).some
  refine hau.nonempty_isColimit_of_pullbackCone_left _ (𝟙 _) _ _ (fun i ↦ ?_)
    (PullbackCone.mk (𝟙 _) f (by simp)) (IsPullback.id_horiz f).isLimit _ (Iso.refl _)
    (by simp) (by simp [c]) (by simp [pullback.condition, c])
  exact pullback.isLimit _ _

set_option backward.isDefEq.respectTransparency false in

-- INSTANCE (free from Core): FinitaryPreExtensive.isIso_sigmaDesc_map

set_option backward.isDefEq.respectTransparency false in

lemma FinitaryPreExtensive.isPullback_sigmaDesc [HasPullbacks C] [FinitaryPreExtensive C]
    {ι ι' : Type*} [Finite ι] [Finite ι'] {S : C} {X : ι → C} {Y : ι' → C}
    (f : ∀ i, X i ⟶ S) (g : ∀ i, Y i ⟶ S) :
    IsPullback
      (Limits.Sigma.desc fun (p : ι × ι') ↦ pullback.fst (f p.1) (g p.2) ≫ Sigma.ι X p.1)
      (Limits.Sigma.desc fun (p : ι × ι') ↦ pullback.snd (f p.1) (g p.2) ≫ Sigma.ι Y p.2)
      (Limits.Sigma.desc f) (Limits.Sigma.desc g) := by
  convert IsUniversalColimit.isPullback_prod_of_isColimit
      (d := Cofan.mk _ (Sigma.ι fun (p : ι × ι') ↦ pullback (f p.1) (g p.2)))
      (hd := coproductIsCoproduct (fun (p : ι × ι') ↦ pullback (f p.1) (g p.2)))
      (a := Cofan.mk _ <| fun i ↦ Sigma.ι _ i) (b := Cofan.mk _ <| fun i ↦ Sigma.ι _ i)
      ?_ ?_ f g (Sigma.desc f) (Sigma.desc g) (fun i j ↦ IsPullback.of_hasPullback (f i) (g j))
  · ext
    simp [Cofan.IsColimit.desc, Sigma.ι, coproductIsCoproduct]
  · ext
    simp [Cofan.IsColimit.desc, Sigma.ι, coproductIsCoproduct]
  · exact FinitaryPreExtensive.isUniversal_finiteCoproducts (coproductIsCoproduct X)
  · exact FinitaryPreExtensive.isUniversal_finiteCoproducts (coproductIsCoproduct Y)

end FiniteCoproducts

end Extensive

end CategoryTheory
