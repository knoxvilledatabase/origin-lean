/-
Extracted from Analysis/Normed/Module/Basic.lean
Genuine: 38 | Conflates: 0 | Dissolved: 0 | Infrastructure: 41
-/
import Origin.Core
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Algebra.Prod
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Algebra.RestrictScalars
import Mathlib.Algebra.Module.Rat
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Normed.MulAction

/-!
# Normed spaces

In this file we define (semi)normed spaces and algebras. We also prove some theorems
about these definitions.
-/

variable {𝕜 𝕜' E F α : Type*}

open Filter Metric Function Set Topology Bornology

open scoped NNReal ENNReal uniformity

section SeminormedAddCommGroup

section Prio

class NormedSpace (𝕜 : Type*) (E : Type*) [NormedField 𝕜] [SeminormedAddCommGroup E]
    extends Module 𝕜 E where
  norm_smul_le : ∀ (a : 𝕜) (b : E), ‖a • b‖ ≤ ‖a‖ * ‖b‖

attribute [inherit_doc NormedSpace] NormedSpace.norm_smul_le

end Prio

variable [NormedField 𝕜] [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]

variable [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]

instance (priority := 100) NormedSpace.boundedSMul [NormedSpace 𝕜 E] : BoundedSMul 𝕜 E :=
  BoundedSMul.of_norm_smul_le NormedSpace.norm_smul_le

instance NormedField.toNormedSpace : NormedSpace 𝕜 𝕜 where norm_smul_le a b := norm_mul_le a b

instance NormedField.to_boundedSMul : BoundedSMul 𝕜 𝕜 :=
  NormedSpace.boundedSMul

variable (𝕜) in

theorem norm_zsmul (n : ℤ) (x : E) : ‖n • x‖ = ‖(n : 𝕜)‖ * ‖x‖ := by
  rw [← norm_smul, ← Int.smul_one_eq_cast, smul_assoc, one_smul]

theorem eventually_nhds_norm_smul_sub_lt (c : 𝕜) (x : E) {ε : ℝ} (h : 0 < ε) :
    ∀ᶠ y in 𝓝 x, ‖c • (y - x)‖ < ε :=
  have : Tendsto (fun y ↦ ‖c • (y - x)‖) (𝓝 x) (𝓝 0) :=
    Continuous.tendsto' (by fun_prop) _ _ (by simp)
  this.eventually (gt_mem_nhds h)

theorem Filter.Tendsto.zero_smul_isBoundedUnder_le {f : α → 𝕜} {g : α → E} {l : Filter α}
    (hf : Tendsto f l (𝓝 0)) (hg : IsBoundedUnder (· ≤ ·) l (Norm.norm ∘ g)) :
    Tendsto (fun x => f x • g x) l (𝓝 0) :=
  hf.op_zero_isBoundedUnder_le hg (· • ·) norm_smul_le

theorem Filter.IsBoundedUnder.smul_tendsto_zero {f : α → 𝕜} {g : α → E} {l : Filter α}
    (hf : IsBoundedUnder (· ≤ ·) l (norm ∘ f)) (hg : Tendsto g l (𝓝 0)) :
    Tendsto (fun x => f x • g x) l (𝓝 0) :=
  hg.op_zero_isBoundedUnder_le hf (flip (· • ·)) fun x y =>
    (norm_smul_le y x).trans_eq (mul_comm _ _)

instance NormedSpace.discreteTopology_zmultiples
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℚ E] (e : E) :
    DiscreteTopology <| AddSubgroup.zmultiples e := by
  rcases eq_or_ne e 0 with (rfl | he)
  · rw [AddSubgroup.zmultiples_zero_eq_bot]
    exact Subsingleton.discreteTopology (α := ↑(⊥ : Subspace ℚ E))
  · rw [discreteTopology_iff_isOpen_singleton_zero, isOpen_induced_iff]
    refine ⟨Metric.ball 0 ‖e‖, Metric.isOpen_ball, ?_⟩
    ext ⟨x, hx⟩
    obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
    rw [mem_preimage, mem_ball_zero_iff, AddSubgroup.coe_mk, mem_singleton_iff, Subtype.ext_iff,
      AddSubgroup.coe_mk, AddSubgroup.coe_zero, norm_zsmul ℚ k e, Int.norm_cast_rat,
      Int.norm_eq_abs, mul_lt_iff_lt_one_left (norm_pos_iff.mpr he), ← @Int.cast_one ℝ _,
      ← Int.cast_abs, Int.cast_lt, Int.abs_lt_one_iff, smul_eq_zero, or_iff_left he]

open NormedField

instance ULift.normedSpace : NormedSpace 𝕜 (ULift E) :=
  { __ := ULift.seminormedAddCommGroup (E := E),
    __ := ULift.module'
    norm_smul_le := fun s x => (norm_smul_le s x.down : _) }

instance Prod.normedSpace : NormedSpace 𝕜 (E × F) :=
  { Prod.seminormedAddCommGroup (E := E) (F := F), Prod.instModule with
    norm_smul_le := fun s x => by
      simp only [norm_smul, Prod.norm_def, Prod.smul_snd, Prod.smul_fst,
        mul_max_of_nonneg, norm_nonneg, le_rfl] }

instance Pi.normedSpace {ι : Type*} {E : ι → Type*} [Fintype ι] [∀ i, SeminormedAddCommGroup (E i)]
    [∀ i, NormedSpace 𝕜 (E i)] : NormedSpace 𝕜 (∀ i, E i) where
  norm_smul_le a f := by
    simp_rw [← coe_nnnorm, ← NNReal.coe_mul, NNReal.coe_le_coe, Pi.nnnorm_def,
      NNReal.mul_finset_sup]
    exact Finset.sup_mono_fun fun _ _ => norm_smul_le a _

instance SeparationQuotient.instNormedSpace : NormedSpace 𝕜 (SeparationQuotient E) where
  norm_smul_le := norm_smul_le

instance MulOpposite.instNormedSpace : NormedSpace 𝕜 Eᵐᵒᵖ where
  norm_smul_le _ x := norm_smul_le _ x.unop

instance Submodule.normedSpace {𝕜 R : Type*} [SMul 𝕜 R] [NormedField 𝕜] [Ring R] {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [Module R E] [IsScalarTower 𝕜 R E]
    (s : Submodule R E) : NormedSpace 𝕜 s where
  norm_smul_le c x := norm_smul_le c (x : E)

variable {S 𝕜 R E : Type*} [SMul 𝕜 R] [NormedField 𝕜] [Ring R] [SeminormedAddCommGroup E]

variable [NormedSpace 𝕜 E] [Module R E] [IsScalarTower 𝕜 R E] [SetLike S E] [AddSubgroupClass S E]

variable [SMulMemClass S R E] (s : S)

instance (priority := 75) SubmoduleClass.toNormedSpace : NormedSpace 𝕜 s where
  norm_smul_le c x := norm_smul_le c (x : E)

end SeminormedAddCommGroup

abbrev NormedSpace.induced {F : Type*} (𝕜 E G : Type*) [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [SeminormedAddCommGroup G] [NormedSpace 𝕜 G] [FunLike F E G] [LinearMapClass F 𝕜 E G] (f : F) :
    @NormedSpace 𝕜 E _ (SeminormedAddCommGroup.induced E G f) :=
  let _ := SeminormedAddCommGroup.induced E G f
  ⟨fun a b ↦ by simpa only [← map_smul f a b] using norm_smul_le a (f b)⟩

section NormedAddCommGroup

variable [NormedField 𝕜]

variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]

variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]

open NormedField

instance (priority := 100) NormedSpace.toModule' : Module 𝕜 F :=
  NormedSpace.toModule

end NormedAddCommGroup

section NontriviallyNormedSpace

variable (𝕜 E)

variable [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [Nontrivial E]

include 𝕜

theorem NormedSpace.exists_lt_norm (c : ℝ) : ∃ x : E, c < ‖x‖ := by
  rcases exists_ne (0 : E) with ⟨x, hx⟩
  rcases NormedField.exists_lt_norm 𝕜 (c / ‖x‖) with ⟨r, hr⟩
  use r • x
  rwa [norm_smul, ← div_lt_iff₀]
  rwa [norm_pos_iff]

protected theorem NormedSpace.unbounded_univ : ¬Bornology.IsBounded (univ : Set E) := fun h =>
  let ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 h
  let ⟨x, hx⟩ := NormedSpace.exists_lt_norm 𝕜 E R
  hx.not_le (hR x trivial)

protected lemma NormedSpace.cobounded_neBot : NeBot (cobounded E) := by
  rw [neBot_iff, Ne, cobounded_eq_bot_iff, ← isBounded_univ]
  exact NormedSpace.unbounded_univ 𝕜 E

instance (priority := 100) NontriviallyNormedField.cobounded_neBot : NeBot (cobounded 𝕜) :=
  NormedSpace.cobounded_neBot 𝕜 𝕜

instance (priority := 80) RealNormedSpace.cobounded_neBot [NormedSpace ℝ E] :
    NeBot (cobounded E) := NormedSpace.cobounded_neBot ℝ E

instance (priority := 80) NontriviallyNormedField.infinite : Infinite 𝕜 :=
  ⟨fun _ ↦ NormedSpace.unbounded_univ 𝕜 𝕜 (Set.toFinite _).isBounded⟩

end NontriviallyNormedSpace

section NormedSpace

variable (𝕜 E)

variable [NormedField 𝕜] [Infinite 𝕜] [NormedAddCommGroup E] [Nontrivial E] [NormedSpace 𝕜 E]

include 𝕜

protected theorem NormedSpace.noncompactSpace : NoncompactSpace E := by
  by_cases H : ∃ c : 𝕜, c ≠ 0 ∧ ‖c‖ ≠ 1
  · letI := NontriviallyNormedField.ofNormNeOne H
    exact ⟨fun h ↦ NormedSpace.unbounded_univ 𝕜 E h.isBounded⟩
  · push_neg at H
    rcases exists_ne (0 : E) with ⟨x, hx⟩
    suffices IsClosedEmbedding (Infinite.natEmbedding 𝕜 · • x) from this.noncompactSpace
    refine isClosedEmbedding_of_pairwise_le_dist (norm_pos_iff.2 hx) fun k n hne ↦ ?_
    simp only [dist_eq_norm, ← sub_smul, norm_smul]
    rw [H, one_mul]
    rwa [sub_ne_zero, (Embedding.injective _).ne_iff]

instance (priority := 100) NormedField.noncompactSpace : NoncompactSpace 𝕜 :=
  NormedSpace.noncompactSpace 𝕜 𝕜

instance (priority := 100) RealNormedSpace.noncompactSpace [NormedSpace ℝ E] : NoncompactSpace E :=
  NormedSpace.noncompactSpace ℝ E

end NormedSpace

section NormedAlgebra

class NormedAlgebra (𝕜 : Type*) (𝕜' : Type*) [NormedField 𝕜] [SeminormedRing 𝕜'] extends
  Algebra 𝕜 𝕜' where
  norm_smul_le : ∀ (r : 𝕜) (x : 𝕜'), ‖r • x‖ ≤ ‖r‖ * ‖x‖

attribute [inherit_doc NormedAlgebra] NormedAlgebra.norm_smul_le

variable (𝕜')

variable [NormedField 𝕜] [SeminormedRing 𝕜'] [NormedAlgebra 𝕜 𝕜']

instance (priority := 100) NormedAlgebra.toNormedSpace : NormedSpace 𝕜 𝕜' :=
  -- Porting note: previous Lean could figure out what we were extending
  { NormedAlgebra.toAlgebra.toModule with
  norm_smul_le := NormedAlgebra.norm_smul_le }

instance (priority := 100) NormedAlgebra.toNormedSpace' {𝕜'} [NormedRing 𝕜'] [NormedAlgebra 𝕜 𝕜'] :
    NormedSpace 𝕜 𝕜' := by infer_instance

theorem norm_algebraMap (x : 𝕜) : ‖algebraMap 𝕜 𝕜' x‖ = ‖x‖ * ‖(1 : 𝕜')‖ := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact norm_smul _ _

theorem nnnorm_algebraMap (x : 𝕜) : ‖algebraMap 𝕜 𝕜' x‖₊ = ‖x‖₊ * ‖(1 : 𝕜')‖₊ :=
  Subtype.ext <| norm_algebraMap 𝕜' x

theorem dist_algebraMap (x y : 𝕜) :
    (dist (algebraMap 𝕜 𝕜' x) (algebraMap 𝕜 𝕜' y)) = dist x y * ‖(1 : 𝕜')‖ := by
  simp only [dist_eq_norm, ← map_sub, norm_algebraMap]

@[simp]
theorem norm_algebraMap' [NormOneClass 𝕜'] (x : 𝕜) : ‖algebraMap 𝕜 𝕜' x‖ = ‖x‖ := by
  rw [norm_algebraMap, norm_one, mul_one]

@[simp]
theorem nnnorm_algebraMap' [NormOneClass 𝕜'] (x : 𝕜) : ‖algebraMap 𝕜 𝕜' x‖₊ = ‖x‖₊ :=
  Subtype.ext <| norm_algebraMap' _ _

@[simp]
theorem dist_algebraMap' [NormOneClass 𝕜'] (x y : 𝕜) :
    (dist (algebraMap 𝕜 𝕜' x) (algebraMap 𝕜 𝕜' y)) = dist x y := by
  simp only [dist_eq_norm, ← map_sub, norm_algebraMap']

section NNReal

variable [NormOneClass 𝕜'] [NormedAlgebra ℝ 𝕜']

@[simp]
theorem norm_algebraMap_nnreal (x : ℝ≥0) : ‖algebraMap ℝ≥0 𝕜' x‖ = x :=
  (norm_algebraMap' 𝕜' (x : ℝ)).symm ▸ Real.norm_of_nonneg x.prop

@[simp]
theorem nnnorm_algebraMap_nnreal (x : ℝ≥0) : ‖algebraMap ℝ≥0 𝕜' x‖₊ = x :=
  Subtype.ext <| norm_algebraMap_nnreal 𝕜' x

end NNReal

variable (𝕜)

theorem algebraMap_isometry [NormOneClass 𝕜'] : Isometry (algebraMap 𝕜 𝕜') := by
  refine Isometry.of_dist_eq fun x y => ?_
  rw [dist_eq_norm, dist_eq_norm, ← RingHom.map_sub, norm_algebraMap']

instance NormedAlgebra.id : NormedAlgebra 𝕜 𝕜 :=
  { NormedField.toNormedSpace, Algebra.id 𝕜 with }

instance normedAlgebraRat {𝕜} [NormedDivisionRing 𝕜] [CharZero 𝕜] [NormedAlgebra ℝ 𝕜] :
    NormedAlgebra ℚ 𝕜 where
  norm_smul_le q x := by
    rw [← smul_one_smul ℝ q x, Rat.smul_one_eq_cast, norm_smul, Rat.norm_cast_real]

instance PUnit.normedAlgebra : NormedAlgebra 𝕜 PUnit where
  norm_smul_le q _ := by simp only [norm_eq_zero, mul_zero, le_refl]

instance : NormedAlgebra 𝕜 (ULift 𝕜') :=
  { ULift.normedSpace, ULift.algebra with }

instance Prod.normedAlgebra {E F : Type*} [SeminormedRing E] [SeminormedRing F] [NormedAlgebra 𝕜 E]
    [NormedAlgebra 𝕜 F] : NormedAlgebra 𝕜 (E × F) :=
  { Prod.normedSpace, Prod.algebra 𝕜 E F with }

instance Pi.normedAlgebra {ι : Type*} {E : ι → Type*} [Fintype ι] [∀ i, SeminormedRing (E i)]
    [∀ i, NormedAlgebra 𝕜 (E i)] : NormedAlgebra 𝕜 (∀ i, E i) :=
  { Pi.normedSpace, Pi.algebra _ E with }

variable [SeminormedRing E] [NormedAlgebra 𝕜 E]

instance SeparationQuotient.instNormedAlgebra : NormedAlgebra 𝕜 (SeparationQuotient E) where
  __ : NormedSpace 𝕜 (SeparationQuotient E) := inferInstance
  __ : Algebra 𝕜 (SeparationQuotient E) := inferInstance

instance MulOpposite.instNormedAlgebra {E : Type*} [SeminormedRing E] [NormedAlgebra 𝕜 E] :
    NormedAlgebra 𝕜 Eᵐᵒᵖ where
  __ := instAlgebra
  __ := instNormedSpace

end NormedAlgebra

abbrev NormedAlgebra.induced {F : Type*} (𝕜 R S : Type*) [NormedField 𝕜] [Ring R] [Algebra 𝕜 R]
    [SeminormedRing S] [NormedAlgebra 𝕜 S] [FunLike F R S] [NonUnitalAlgHomClass F 𝕜 R S]
    (f : F) :
    @NormedAlgebra 𝕜 R _ (SeminormedRing.induced R S f) :=
  letI := SeminormedRing.induced R S f
  ⟨fun a b ↦ show ‖f (a • b)‖ ≤ ‖a‖ * ‖f b‖ from (map_smul f a b).symm ▸ norm_smul_le a (f b)⟩

instance Subalgebra.toNormedAlgebra {𝕜 A : Type*} [SeminormedRing A] [NormedField 𝕜]
    [NormedAlgebra 𝕜 A] (S : Subalgebra 𝕜 A) : NormedAlgebra 𝕜 S :=
  NormedAlgebra.induced 𝕜 S A S.val

section SubalgebraClass

variable {S 𝕜 E : Type*} [NormedField 𝕜] [SeminormedRing E] [NormedAlgebra 𝕜 E]

variable [SetLike S E] [SubringClass S E] [SMulMemClass S 𝕜 E] (s : S)

instance (priority := 75) SubalgebraClass.toNormedAlgebra : NormedAlgebra 𝕜 s where
  norm_smul_le c x := norm_smul_le c (x : E)

end SubalgebraClass

section RestrictScalars

section NormInstances

instance [I : SeminormedAddCommGroup E] :
    SeminormedAddCommGroup (RestrictScalars 𝕜 𝕜' E) :=
  I

instance [I : NormedAddCommGroup E] :
    NormedAddCommGroup (RestrictScalars 𝕜 𝕜' E) :=
  I

instance [I : NonUnitalSeminormedRing E] :
    NonUnitalSeminormedRing (RestrictScalars 𝕜 𝕜' E) :=
  I

instance [I : NonUnitalNormedRing E] :
    NonUnitalNormedRing (RestrictScalars 𝕜 𝕜' E) :=
  I

instance [I : SeminormedRing E] :
    SeminormedRing (RestrictScalars 𝕜 𝕜' E) :=
  I

instance [I : NormedRing E] :
    NormedRing (RestrictScalars 𝕜 𝕜' E) :=
  I

instance [I : NonUnitalSeminormedCommRing E] :
    NonUnitalSeminormedCommRing (RestrictScalars 𝕜 𝕜' E) :=
  I

instance [I : NonUnitalNormedCommRing E] :
    NonUnitalNormedCommRing (RestrictScalars 𝕜 𝕜' E) :=
  I

instance [I : SeminormedCommRing E] :
    SeminormedCommRing (RestrictScalars 𝕜 𝕜' E) :=
  I

instance [I : NormedCommRing E] :
    NormedCommRing (RestrictScalars 𝕜 𝕜' E) :=
  I

end NormInstances

section NormedSpace

variable (𝕜 𝕜' E)

variable [NormedField 𝕜] [NormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
  [SeminormedAddCommGroup E] [NormedSpace 𝕜' E]

instance RestrictScalars.normedSpace : NormedSpace 𝕜 (RestrictScalars 𝕜 𝕜' E) :=
  { RestrictScalars.module 𝕜 𝕜' E with
    norm_smul_le := fun c x =>
      (norm_smul_le (algebraMap 𝕜 𝕜' c) (_ : E)).trans_eq <| by rw [norm_algebraMap'] }

def Module.RestrictScalars.normedSpaceOrig {𝕜 : Type*} {𝕜' : Type*} {E : Type*} [NormedField 𝕜']
    [SeminormedAddCommGroup E] [I : NormedSpace 𝕜' E] : NormedSpace 𝕜' (RestrictScalars 𝕜 𝕜' E) :=
  I

abbrev NormedSpace.restrictScalars : NormedSpace 𝕜 E :=
  RestrictScalars.normedSpace _ 𝕜' E

end NormedSpace

section NormedAlgebra

variable (𝕜 𝕜' E)

variable [NormedField 𝕜] [NormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
  [SeminormedRing E] [NormedAlgebra 𝕜' E]

instance RestrictScalars.normedAlgebra : NormedAlgebra 𝕜 (RestrictScalars 𝕜 𝕜' E) :=
  { RestrictScalars.algebra 𝕜 𝕜' E with
    norm_smul_le := norm_smul_le }

def Module.RestrictScalars.normedAlgebraOrig {𝕜 : Type*} {𝕜' : Type*} {E : Type*} [NormedField 𝕜']
    [SeminormedRing E] [I : NormedAlgebra 𝕜' E] : NormedAlgebra 𝕜' (RestrictScalars 𝕜 𝕜' E) :=
  I

abbrev NormedAlgebra.restrictScalars : NormedAlgebra 𝕜 E :=
  RestrictScalars.normedAlgebra _ 𝕜' _

end NormedAlgebra

end RestrictScalars

section Core

/-!
### Structures for constructing new normed spaces

This section contains tools meant for constructing new normed spaces. These allow one to easily
construct all the relevant instances (distances measures, etc) while proving only a minimal
set of axioms. Furthermore, tools are provided to add a norm structure to a type that already
has a preexisting uniformity or bornology: in such cases, it is necessary to keep the preexisting
instances, while ensuring that the norm induces the same uniformity/bornology.
-/

open scoped Uniformity Bornology

structure SeminormedAddCommGroup.Core (𝕜 : Type*) (E : Type*) [NormedField 𝕜] [AddCommGroup E]
    [Norm E] [Module 𝕜 E] : Prop where
  norm_nonneg (x : E) : 0 ≤ ‖x‖
  norm_smul (c : 𝕜) (x : E) : ‖c • x‖ = ‖c‖ * ‖x‖
  norm_triangle (x y : E) : ‖x + y‖ ≤ ‖x‖ + ‖y‖

abbrev PseudoMetricSpace.ofSeminormedAddCommGroupCore {𝕜 E : Type*} [NormedField 𝕜] [AddCommGroup E]
    [Norm E] [Module 𝕜 E] (core : SeminormedAddCommGroup.Core 𝕜 E) :
    PseudoMetricSpace E where
  dist x y := ‖x - y‖
  dist_self x := by
    show ‖x - x‖ = 0
    simp only [sub_self]
    have : (0 : E) = (0 : 𝕜) • (0 : E) := by simp
    rw [this, core.norm_smul]
    simp
  dist_comm x y := by
    show ‖x - y‖ = ‖y - x‖
    have : y - x = (-1 : 𝕜) • (x - y) := by simp
    rw [this, core.norm_smul]
    simp
  dist_triangle x y z := by
    show ‖x - z‖ ≤ ‖x - y‖ + ‖y - z‖
    have : x - z = (x - y) + (y - z) := by abel
    rw [this]
    exact core.norm_triangle _ _
  edist_dist x y := by exact (ENNReal.ofReal_eq_coe_nnreal _).symm

abbrev PseudoEMetricSpace.ofSeminormedAddCommGroupCore {𝕜 E : Type*} [NormedField 𝕜]
    [AddCommGroup E] [Norm E] [Module 𝕜 E]
    (core : SeminormedAddCommGroup.Core 𝕜 E) : PseudoEMetricSpace E :=
  (PseudoMetricSpace.ofSeminormedAddCommGroupCore core).toPseudoEMetricSpace

abbrev PseudoMetricSpace.ofSeminormedAddCommGroupCoreReplaceUniformity {𝕜 E : Type*} [NormedField 𝕜]
    [AddCommGroup E] [Norm E] [Module 𝕜 E] [U : UniformSpace E]
    (core : SeminormedAddCommGroup.Core 𝕜 E)
    (H : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace
        (self := PseudoEMetricSpace.ofSeminormedAddCommGroupCore core)]) :
    PseudoMetricSpace E :=
  .replaceUniformity (.ofSeminormedAddCommGroupCore core) H

open Bornology in

abbrev PseudoMetricSpace.ofSeminormedAddCommGroupCoreReplaceAll {𝕜 E : Type*} [NormedField 𝕜]
    [AddCommGroup E] [Norm E] [Module 𝕜 E] [U : UniformSpace E] [B : Bornology E]
    (core : SeminormedAddCommGroup.Core 𝕜 E)
    (HU : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace
      (self := PseudoEMetricSpace.ofSeminormedAddCommGroupCore core)])
    (HB : ∀ s : Set E, @IsBounded _ B s
      ↔ @IsBounded _ (PseudoMetricSpace.ofSeminormedAddCommGroupCore core).toBornology s) :
    PseudoMetricSpace E :=
  .replaceBornology (.replaceUniformity (.ofSeminormedAddCommGroupCore core) HU) HB

abbrev SeminormedAddCommGroup.ofCore {𝕜 : Type*} {E : Type*} [NormedField 𝕜] [AddCommGroup E]
    [Norm E] [Module 𝕜 E] (core : SeminormedAddCommGroup.Core 𝕜 E) : SeminormedAddCommGroup E :=
  { PseudoMetricSpace.ofSeminormedAddCommGroupCore core with }

abbrev SeminormedAddCommGroup.ofCoreReplaceUniformity {𝕜 : Type*} {E : Type*} [NormedField 𝕜]
    [AddCommGroup E] [Norm E] [Module 𝕜 E] [U : UniformSpace E]
    (core : SeminormedAddCommGroup.Core 𝕜 E)
    (H : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace
      (self := PseudoEMetricSpace.ofSeminormedAddCommGroupCore core)]) :
    SeminormedAddCommGroup E :=
  { PseudoMetricSpace.ofSeminormedAddCommGroupCoreReplaceUniformity core H with }

open Bornology in

abbrev SeminormedAddCommGroup.ofCoreReplaceAll {𝕜 : Type*} {E : Type*} [NormedField 𝕜]
    [AddCommGroup E] [Norm E] [Module 𝕜 E] [U : UniformSpace E] [B : Bornology E]
    (core : SeminormedAddCommGroup.Core 𝕜 E)
    (HU : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace
      (self := PseudoEMetricSpace.ofSeminormedAddCommGroupCore core)])
    (HB : ∀ s : Set E, @IsBounded _ B s
      ↔ @IsBounded _ (PseudoMetricSpace.ofSeminormedAddCommGroupCore core).toBornology s) :
    SeminormedAddCommGroup E :=
  { PseudoMetricSpace.ofSeminormedAddCommGroupCoreReplaceAll core HU HB with }

structure NormedSpace.Core (𝕜 : Type*) (E : Type*) [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [Norm E] extends SeminormedAddCommGroup.Core 𝕜 E : Prop where
  norm_eq_zero_iff (x : E) : ‖x‖ = 0 ↔ x = 0

variable {𝕜 : Type*} {E : Type*} [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [Norm E]

abbrev NormedAddCommGroup.ofCore (core : NormedSpace.Core 𝕜 E) : NormedAddCommGroup E :=
  { SeminormedAddCommGroup.ofCore core.toCore with
    eq_of_dist_eq_zero := by
      intro x y h
      rw [← sub_eq_zero, ← core.norm_eq_zero_iff]
      exact h }

abbrev NormedAddCommGroup.ofCoreReplaceUniformity [U : UniformSpace E] (core : NormedSpace.Core 𝕜 E)
    (H : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace
      (self := PseudoEMetricSpace.ofSeminormedAddCommGroupCore core.toCore)]) :
    NormedAddCommGroup E :=
  { SeminormedAddCommGroup.ofCoreReplaceUniformity core.toCore H with
    eq_of_dist_eq_zero := by
      intro x y h
      rw [← sub_eq_zero, ← core.norm_eq_zero_iff]
      exact h }

open Bornology in

abbrev NormedAddCommGroup.ofCoreReplaceAll [U : UniformSpace E] [B : Bornology E]
    (core : NormedSpace.Core 𝕜 E)
    (HU : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace
      (self := PseudoEMetricSpace.ofSeminormedAddCommGroupCore core.toCore)])
    (HB : ∀ s : Set E, @IsBounded _ B s
      ↔ @IsBounded _ (PseudoMetricSpace.ofSeminormedAddCommGroupCore core.toCore).toBornology s) :
    NormedAddCommGroup E :=
  { SeminormedAddCommGroup.ofCoreReplaceAll core.toCore HU HB with
    eq_of_dist_eq_zero := by
      intro x y h
      rw [← sub_eq_zero, ← core.norm_eq_zero_iff]
      exact h }

abbrev NormedSpace.ofCore {𝕜 : Type*} {E : Type*} [NormedField 𝕜] [SeminormedAddCommGroup E]
    [Module 𝕜 E] (core : NormedSpace.Core 𝕜 E) : NormedSpace 𝕜 E where
  norm_smul_le r x := by rw [core.norm_smul r x]

end Core
