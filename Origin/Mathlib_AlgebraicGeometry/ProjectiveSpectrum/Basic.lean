/-
Extracted from AlgebraicGeometry/ProjectiveSpectrum/Basic.lean
Genuine: 31 | Conflates: 0 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import Mathlib.AlgebraicGeometry.AffineScheme

/-!

# Basic properties of the scheme `Proj A`

The scheme `Proj 𝒜` for a graded algebra `𝒜` is constructed in
`AlgebraicGeometry/ProjectiveSpectrum/Scheme.lean`.
In this file we provide basic properties of the scheme.

## Main results
- `AlgebraicGeometry.Proj.toSpecZero`: The structure map `Proj A ⟶ Spec (A 0)`.
- `AlgebraicGeometry.Proj.basicOpenIsoSpec`:
  The canonical isomorphism `Proj A |_ D₊(f) ≅ Spec (A_f)₀`
  when `f` is homogeneous of positive degree.
- `AlgebraicGeometry.Proj.awayι`: The open immersion `Spec (A_f)₀ ⟶ Proj A`.
- `AlgebraicGeometry.Proj.affineOpenCover`: The open cover of `Proj A` by `Spec (A_f)₀` for all
  homogeneous `f` of positive degree.
- `AlgebraicGeometry.Proj.stalkIso`:
The stalk of `Proj A` at `x` is the degree `0` part of the localization of `A` at `x`.

-/

namespace AlgebraicGeometry.Proj

open HomogeneousLocalization CategoryTheory

variable {R A : Type*}

variable [CommRing R] [CommRing A] [Algebra R A]

variable (𝒜 : ℕ → Submodule R A)

variable [GradedAlgebra 𝒜]

section basicOpen

variable (f g : A)

def basicOpen : (Proj 𝒜).Opens :=
  ProjectiveSpectrum.basicOpen 𝒜 f

@[simp]
theorem mem_basicOpen (x : Proj 𝒜) :
    x ∈ basicOpen 𝒜 f ↔ f ∉ x.asHomogeneousIdeal :=
  Iff.rfl

@[simp] theorem basicOpen_one : basicOpen 𝒜 1 = ⊤ := ProjectiveSpectrum.basicOpen_one ..

@[simp] theorem basicOpen_zero : basicOpen 𝒜 0 = ⊥ := ProjectiveSpectrum.basicOpen_zero ..

@[simp] theorem basicOpen_pow (n) (hn : 0 < n) : basicOpen 𝒜 (f ^ n) = basicOpen 𝒜 f :=
  ProjectiveSpectrum.basicOpen_pow 𝒜 f n hn

theorem basicOpen_mul : basicOpen 𝒜 (f * g) = basicOpen 𝒜 f ⊓ basicOpen 𝒜 g :=
  ProjectiveSpectrum.basicOpen_mul ..

theorem basicOpen_mono (hfg : f ∣ g) : basicOpen 𝒜 g ≤ basicOpen 𝒜 f :=
  (hfg.choose_spec ▸ basicOpen_mul 𝒜 f _).trans_le inf_le_left

theorem basicOpen_eq_iSup_proj (f : A) :
    basicOpen 𝒜 f = ⨆ i : ℕ, basicOpen 𝒜 (GradedAlgebra.proj 𝒜 i f) :=
  ProjectiveSpectrum.basicOpen_eq_union_of_projection ..

theorem isBasis_basicOpen :
    TopologicalSpace.Opens.IsBasis (Set.range (basicOpen 𝒜)) := by
  delta TopologicalSpace.Opens.IsBasis
  convert ProjectiveSpectrum.isTopologicalBasis_basic_opens 𝒜
  exact (Set.range_comp _ _).symm

lemma iSup_basicOpen_eq_top {ι : Type*} (f : ι → A)
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤ Ideal.span (Set.range f)) :
    ⨆ i, Proj.basicOpen 𝒜 (f i) = ⊤ := by
  classical
  refine top_le_iff.mp fun x hx ↦ TopologicalSpace.Opens.mem_iSup.mpr ?_
  by_contra! H
  simp only [mem_basicOpen, Decidable.not_not] at H
  refine x.not_irrelevant_le (hf.trans ?_)
  rwa [Ideal.span_le, Set.range_subset_iff]

def awayToSection : CommRingCat.of (Away 𝒜 f) ⟶ Γ(Proj 𝒜, basicOpen 𝒜 f) :=
  ProjectiveSpectrum.Proj.awayToSection ..

noncomputable

def basicOpenToSpec : (basicOpen 𝒜 f).toScheme ⟶ Spec (.of (Away 𝒜 f)) :=
  (basicOpen 𝒜 f).toSpecΓ ≫ Spec.map (awayToSection 𝒜 f)

lemma basicOpenToSpec_app_top :
    (basicOpenToSpec 𝒜 f).app ⊤ = (Scheme.ΓSpecIso _).hom ≫ awayToSection 𝒜 f ≫
      (basicOpen 𝒜 f).topIso.inv := by
  rw [basicOpenToSpec]
  simp only [Scheme.comp_coeBase, TopologicalSpace.Opens.map_comp_obj,
    TopologicalSpace.Opens.map_top, Scheme.comp_app, Scheme.Opens.topIso_inv, eqToHom_op]
  erw [Scheme.comp_app]
  simp

noncomputable

def toSpecZero : Proj 𝒜 ⟶ Spec (.of (𝒜 0)) :=
  (Scheme.topIso _).inv ≫ (Scheme.isoOfEq _ (basicOpen_one _)).inv ≫
    basicOpenToSpec 𝒜 1 ≫ Spec.map (fromZeroRingHom 𝒜 _)

variable {m} (f_deg : f ∈ 𝒜 m) (hm : 0 < m)

noncomputable

@[simps! (config := .lemmasOnly) hom]
def basicOpenIsoSpec : (basicOpen 𝒜 f).toScheme ≅ Spec (.of (Away 𝒜 f)) :=
  have : IsIso (basicOpenToSpec 𝒜 f) := by
    apply (isIso_iff_of_reflects_iso _ Scheme.forgetToLocallyRingedSpace).mp ?_
    convert ProjectiveSpectrum.Proj.isIso_toSpec 𝒜 f f_deg hm using 1
    refine Eq.trans ?_ (ΓSpec.locallyRingedSpaceAdjunction.homEquiv_apply _ _ _).symm
    dsimp [basicOpenToSpec, Scheme.Opens.toSpecΓ]
    simp only [eqToHom_op, Category.assoc, ← Spec.map_comp]
    rfl
  asIso (basicOpenToSpec 𝒜 f)

noncomputable

@[simps! (config := .lemmasOnly) hom]
def basicOpenIsoAway : CommRingCat.of (Away 𝒜 f) ≅ Γ(Proj 𝒜, basicOpen 𝒜 f) :=
  have : IsIso (awayToSection 𝒜 f) := by
    have := basicOpenToSpec_app_top 𝒜 f
    rw [← Iso.inv_comp_eq, Iso.eq_comp_inv] at this
    rw [← this, ← basicOpenIsoSpec_hom 𝒜 f f_deg hm]
    infer_instance
  asIso (awayToSection 𝒜 f)

noncomputable

def awayι : Spec (.of (Away 𝒜 f)) ⟶ Proj 𝒜 :=
  (basicOpenIsoSpec 𝒜 f f_deg hm).inv ≫ (Proj.basicOpen 𝒜 f).ι

instance : IsOpenImmersion (Proj.awayι 𝒜 f f_deg hm) :=
  IsOpenImmersion.comp _ _

lemma opensRange_awayι :
    (Proj.awayι 𝒜 f f_deg hm).opensRange = Proj.basicOpen 𝒜 f :=
  (Scheme.Hom.opensRange_comp_of_isIso _ _).trans (basicOpen 𝒜 f).opensRange_ι

include f_deg hm in

lemma isAffineOpen_basicOpen : IsAffineOpen (basicOpen 𝒜 f) := by
  rw [← opensRange_awayι 𝒜 f f_deg hm]
  exact isAffineOpen_opensRange (awayι _ _ _ _)

@[reassoc]
lemma awayι_toSpecZero : awayι 𝒜 f f_deg hm ≫ toSpecZero 𝒜 =
    Spec.map (CommRingCat.ofHom (fromZeroRingHom 𝒜 _)) := by
  rw [toSpecZero, basicOpenToSpec, awayι]
  simp only [Category.assoc, Iso.inv_comp_eq, basicOpenIsoSpec_hom]
  have (U) (e : U = ⊤) : (basicOpen 𝒜 f).ι ≫ (Scheme.topIso _).inv ≫ (Scheme.isoOfEq _ e).inv =
      Scheme.homOfLE _ (le_top.trans_eq e.symm) := by
    simp only [← Category.assoc, Iso.comp_inv_eq]
    simp only [Scheme.topIso_hom, Category.assoc, Scheme.isoOfEq_hom_ι, Scheme.homOfLE_ι]
  rw [reassoc_of% this, ← Scheme.Opens.toSpecΓ_SpecMap_map_assoc, basicOpenToSpec, Category.assoc,
    ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
  rfl

variable {f}

variable {m' : ℕ} {g : A} (g_deg : g ∈ 𝒜 m') (hm' : 0 < m') {x : A} (hx : x = f * g)

@[reassoc]
lemma awayMap_awayToSection  :
    CommRingCat.ofHom (awayMap 𝒜 g_deg hx) ≫ awayToSection 𝒜 x =
      awayToSection 𝒜 f ≫ (Proj 𝒜).presheaf.map (homOfLE (basicOpen_mono _ _ _ ⟨_, hx⟩)).op := by
  ext a
  apply Subtype.ext
  ext ⟨i, hi⟩
  obtain ⟨⟨n, a, ⟨b, hb'⟩, i, rfl : _ = b⟩, rfl⟩ := mk_surjective a
  simp only [CommRingCat.forget_obj, CommRingCat.coe_of, CommRingCat.ofHom, CommRingCat.coe_comp_of,
    RingHom.coe_comp, Function.comp_apply, homOfLE_leOfHom]
  erw [ProjectiveSpectrum.Proj.awayToSection_apply]
  rw [val_awayMap_mk, Localization.mk_eq_mk', IsLocalization.map_mk',
    ← Localization.mk_eq_mk']
  refine Localization.mk_eq_mk_iff.mpr ?_
  rw [Localization.r_iff_exists]
  use 1
  simp only [OneMemClass.coe_one, RingHom.id_apply, one_mul, hx]
  ring

@[reassoc]
lemma basicOpenToSpec_SpecMap_awayMap :
    basicOpenToSpec 𝒜 x ≫ Spec.map (CommRingCat.ofHom (awayMap 𝒜 g_deg hx)) =
      (Proj 𝒜).homOfLE (basicOpen_mono _ _ _ ⟨_, hx⟩) ≫ basicOpenToSpec 𝒜 f := by
  rw [basicOpenToSpec, Category.assoc, ← Spec.map_comp, awayMap_awayToSection,
    Spec.map_comp, Scheme.Opens.toSpecΓ_SpecMap_map_assoc]
  rfl

@[reassoc]
lemma SpecMap_awayMap_awayι :
    Spec.map (CommRingCat.ofHom (awayMap 𝒜 g_deg hx)) ≫ awayι 𝒜 f f_deg hm =
      awayι 𝒜 x (hx ▸ SetLike.mul_mem_graded f_deg g_deg) (hm.trans_le (m.le_add_right m')) := by
  rw [awayι, awayι, Iso.eq_inv_comp, basicOpenIsoSpec_hom, basicOpenToSpec_SpecMap_awayMap_assoc,
  ← basicOpenIsoSpec_hom _ _ f_deg hm, Iso.hom_inv_id_assoc, Scheme.homOfLE_ι]

noncomputable

def pullbackAwayιIso :
    Limits.pullback (awayι 𝒜 f f_deg hm) (awayι 𝒜 g g_deg hm') ≅
      Spec (CommRingCat.of (Away 𝒜 x)) :=
    IsOpenImmersion.isoOfRangeEq (Limits.pullback.fst _ _ ≫ awayι 𝒜 f f_deg hm)
      (awayι 𝒜 x (hx ▸ SetLike.mul_mem_graded f_deg g_deg) (hm.trans_le (m.le_add_right m'))) <| by
  rw [IsOpenImmersion.range_pullback_to_base_of_left]
  show ((awayι 𝒜 f _ _).opensRange ⊓ (awayι 𝒜 g _ _).opensRange).1 = (awayι 𝒜 _ _ _).opensRange.1
  rw [opensRange_awayι, opensRange_awayι, opensRange_awayι, ← basicOpen_mul, hx]

@[reassoc (attr := simp)]
lemma pullbackAwayιIso_hom_awayι :
    (pullbackAwayιIso 𝒜 f_deg hm g_deg hm' hx).hom ≫
      awayι 𝒜 x (hx ▸ SetLike.mul_mem_graded f_deg g_deg) (hm.trans_le (m.le_add_right m')) =
      Limits.pullback.fst _ _ ≫ awayι 𝒜 f f_deg hm :=
  IsOpenImmersion.isoOfRangeEq_hom_fac ..

@[reassoc (attr := simp)]
lemma pullbackAwayιIso_hom_SpecMap_awayMap_left :
    (pullbackAwayιIso 𝒜 f_deg hm g_deg hm' hx).hom ≫
      Spec.map (CommRingCat.ofHom (awayMap 𝒜 g_deg hx)) = Limits.pullback.fst _ _ := by
  rw [← cancel_mono (awayι 𝒜 f f_deg hm), ← pullbackAwayιIso_hom_awayι,
    Category.assoc, SpecMap_awayMap_awayι]

@[reassoc (attr := simp)]
lemma pullbackAwayιIso_hom_SpecMap_awayMap_right :
    (pullbackAwayιIso 𝒜 f_deg hm g_deg hm' hx).hom ≫
      Spec.map (CommRingCat.ofHom (awayMap 𝒜 f_deg (hx.trans (mul_comm _ _)))) =
      Limits.pullback.snd _ _ := by
  rw [← cancel_mono (awayι 𝒜 g g_deg hm'), ← Limits.pullback.condition,
    ← pullbackAwayιIso_hom_awayι 𝒜 f_deg hm g_deg hm' hx,
    Category.assoc, SpecMap_awayMap_awayι]
  rfl

@[reassoc (attr := simp)]
lemma pullbackAwayιIso_inv_fst :
    (pullbackAwayιIso 𝒜 f_deg hm g_deg hm' hx).inv ≫ Limits.pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (awayMap 𝒜 g_deg hx)) := by
  rw [← pullbackAwayιIso_hom_SpecMap_awayMap_left, Iso.inv_hom_id_assoc]

@[reassoc (attr := simp)]
lemma pullbackAwayιIso_inv_snd :
    (pullbackAwayιIso 𝒜 f_deg hm g_deg hm' hx).inv ≫ Limits.pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (awayMap 𝒜 f_deg (hx.trans (mul_comm _ _)))) := by
  rw [← pullbackAwayιIso_hom_SpecMap_awayMap_right, Iso.inv_hom_id_assoc]

open TopologicalSpace.Opens in

noncomputable

def openCoverOfISupEqTop {ι : Type*} (f : ι → A) {m : ι → ℕ}
    (f_deg : ∀ i, f i ∈ 𝒜 (m i)) (hm : ∀ i, 0 < m i)
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤ Ideal.span (Set.range f)) :
    (Proj 𝒜).AffineOpenCover where
  J := ι
  obj i := .of (Away 𝒜 (f i))
  map i := awayι 𝒜 (f i) (f_deg i) (hm i)
  f x := (mem_iSup.mp ((iSup_basicOpen_eq_top 𝒜 f hf).ge (Set.mem_univ x))).choose
  covers x := by
    show x ∈ (awayι 𝒜 _ _ _).opensRange
    rw [opensRange_awayι]
    exact (mem_iSup.mp ((iSup_basicOpen_eq_top 𝒜 f hf).ge (Set.mem_univ x))).choose_spec

noncomputable

def affineOpenCover : (Proj 𝒜).AffineOpenCover :=
  openCoverOfISupEqTop 𝒜 (ι := Σ i : PNat, 𝒜 i) (m := fun i ↦ i.1) (fun i ↦ i.2) (fun i ↦ i.2.2)
    (fun i ↦ i.1.2) <| by
  classical
  intro z hz
  rw [← DirectSum.sum_support_decompose 𝒜 z]
  refine Ideal.sum_mem _ fun c hc ↦ if hc0 : c = 0 then ?_ else
    Ideal.subset_span ⟨⟨⟨c, Nat.pos_iff_ne_zero.mpr hc0⟩, _⟩, rfl⟩
  convert Ideal.zero_mem _
  subst hc0
  exact hz

end basicOpen

section stalk

noncomputable

def stalkIso (x : Proj 𝒜) :
    (Proj 𝒜).presheaf.stalk x ≅ .of (AtPrime 𝒜 x.asHomogeneousIdeal.toIdeal) :=
  (stalkIso' 𝒜 x).toCommRingCatIso

end stalk

end AlgebraicGeometry.Proj
