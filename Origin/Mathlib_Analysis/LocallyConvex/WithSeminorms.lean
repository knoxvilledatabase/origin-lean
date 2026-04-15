/-
Extracted from Analysis/LocallyConvex/WithSeminorms.lean
Genuine: 68 of 74 | Dissolved: 4 | Infrastructure: 2
-/
import Origin.Core
import Mathlib.Analysis.LocallyConvex.Bounded
import Mathlib.Analysis.Seminorm
import Mathlib.Data.Real.Sqrt
import Mathlib.Topology.Algebra.Equicontinuity
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.Algebra.FilterBasis
import Mathlib.Topology.Algebra.Module.LocallyConvex

/-!
# Topology induced by a family of seminorms

## Main definitions

* `SeminormFamily.basisSets`: The set of open seminorm balls for a family of seminorms.
* `SeminormFamily.moduleFilterBasis`: A module filter basis formed by the open balls.
* `Seminorm.IsBounded`: A linear map `f : E →ₗ[𝕜] F` is bounded iff every seminorm in `F` can be
bounded by a finite number of seminorms in `E`.

## Main statements

* `WithSeminorms.toLocallyConvexSpace`: A space equipped with a family of seminorms is locally
convex.
* `WithSeminorms.firstCountable`: A space is first countable if it's topology is induced by a
countable family of seminorms.

## Continuity of semilinear maps

If `E` and `F` are topological vector space with the topology induced by a family of seminorms, then
we have a direct method to prove that a linear map is continuous:
* `Seminorm.continuous_from_bounded`: A bounded linear map `f : E →ₗ[𝕜] F` is continuous.

If the topology of a space `E` is induced by a family of seminorms, then we can characterize von
Neumann boundedness in terms of that seminorm family. Together with
`LinearMap.continuous_of_locally_bounded` this gives general criterion for continuity.

* `WithSeminorms.isVonNBounded_iff_finset_seminorm_bounded`
* `WithSeminorms.isVonNBounded_iff_seminorm_bounded`
* `WithSeminorms.image_isVonNBounded_iff_finset_seminorm_bounded`
* `WithSeminorms.image_isVonNBounded_iff_seminorm_bounded`

## Tags

seminorm, locally convex
-/

open NormedField Set Seminorm TopologicalSpace Filter List

open NNReal Pointwise Topology Uniformity

variable {𝕜 𝕜₂ 𝕝 𝕝₂ E F G ι ι' : Type*}

section FilterBasis

variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

variable (𝕜 E ι)

abbrev SeminormFamily :=
  ι → Seminorm 𝕜 E

variable {𝕜 E ι}

namespace SeminormFamily

def basisSets (p : SeminormFamily 𝕜 E ι) : Set (Set E) :=
  ⋃ (s : Finset ι) (r) (_ : 0 < r), singleton (ball (s.sup p) (0 : E) r)

variable (p : SeminormFamily 𝕜 E ι)

theorem basisSets_iff {U : Set E} :
    U ∈ p.basisSets ↔ ∃ (i : Finset ι) (r : ℝ), 0 < r ∧ U = ball (i.sup p) 0 r := by
  simp only [basisSets, mem_iUnion, exists_prop, mem_singleton_iff]

theorem basisSets_mem (i : Finset ι) {r : ℝ} (hr : 0 < r) : (i.sup p).ball 0 r ∈ p.basisSets :=
  (basisSets_iff _).mpr ⟨i, _, hr, rfl⟩

theorem basisSets_singleton_mem (i : ι) {r : ℝ} (hr : 0 < r) : (p i).ball 0 r ∈ p.basisSets :=
  (basisSets_iff _).mpr ⟨{i}, _, hr, by rw [Finset.sup_singleton]⟩

theorem basisSets_nonempty [Nonempty ι] : p.basisSets.Nonempty := by
  let i := Classical.arbitrary ι
  refine nonempty_def.mpr ⟨(p i).ball 0 1, ?_⟩
  exact p.basisSets_singleton_mem i zero_lt_one

theorem basisSets_intersect (U V : Set E) (hU : U ∈ p.basisSets) (hV : V ∈ p.basisSets) :
    ∃ z ∈ p.basisSets, z ⊆ U ∩ V := by
  classical
    rcases p.basisSets_iff.mp hU with ⟨s, r₁, hr₁, hU⟩
    rcases p.basisSets_iff.mp hV with ⟨t, r₂, hr₂, hV⟩
    use ((s ∪ t).sup p).ball 0 (min r₁ r₂)
    refine ⟨p.basisSets_mem (s ∪ t) (lt_min_iff.mpr ⟨hr₁, hr₂⟩), ?_⟩
    rw [hU, hV, ball_finset_sup_eq_iInter _ _ _ (lt_min_iff.mpr ⟨hr₁, hr₂⟩),
      ball_finset_sup_eq_iInter _ _ _ hr₁, ball_finset_sup_eq_iInter _ _ _ hr₂]
    exact
      Set.subset_inter
        (Set.iInter₂_mono' fun i hi =>
          ⟨i, Finset.subset_union_left hi, ball_mono <| min_le_left _ _⟩)
        (Set.iInter₂_mono' fun i hi =>
          ⟨i, Finset.subset_union_right hi, ball_mono <| min_le_right _ _⟩)

theorem basisSets_zero (U) (hU : U ∈ p.basisSets) : (0 : E) ∈ U := by
  rcases p.basisSets_iff.mp hU with ⟨ι', r, hr, hU⟩
  rw [hU, mem_ball_zero, map_zero]
  exact hr

theorem basisSets_add (U) (hU : U ∈ p.basisSets) :
    ∃ V ∈ p.basisSets, V + V ⊆ U := by
  rcases p.basisSets_iff.mp hU with ⟨s, r, hr, hU⟩
  use (s.sup p).ball 0 (r / 2)
  refine ⟨p.basisSets_mem s (div_pos hr zero_lt_two), ?_⟩
  refine Set.Subset.trans (ball_add_ball_subset (s.sup p) (r / 2) (r / 2) 0 0) ?_
  rw [hU, add_zero, add_halves]

theorem basisSets_neg (U) (hU' : U ∈ p.basisSets) :
    ∃ V ∈ p.basisSets, V ⊆ (fun x : E => -x) ⁻¹' U := by
  rcases p.basisSets_iff.mp hU' with ⟨s, r, _, hU⟩
  rw [hU, neg_preimage, neg_ball (s.sup p), neg_zero]
  exact ⟨U, hU', Eq.subset hU⟩

protected def addGroupFilterBasis [Nonempty ι] : AddGroupFilterBasis E :=
  addGroupFilterBasisOfComm p.basisSets p.basisSets_nonempty p.basisSets_intersect p.basisSets_zero
    p.basisSets_add p.basisSets_neg

theorem basisSets_smul_right (v : E) (U : Set E) (hU : U ∈ p.basisSets) :
    ∀ᶠ x : 𝕜 in 𝓝 0, x • v ∈ U := by
  rcases p.basisSets_iff.mp hU with ⟨s, r, hr, hU⟩
  rw [hU, Filter.eventually_iff]
  simp_rw [(s.sup p).mem_ball_zero, map_smul_eq_mul]
  by_cases h : 0 < (s.sup p) v
  · simp_rw [(lt_div_iff₀ h).symm]
    rw [← _root_.ball_zero_eq]
    exact Metric.ball_mem_nhds 0 (div_pos hr h)
  simp_rw [le_antisymm (not_lt.mp h) (apply_nonneg _ v), mul_zero, hr]
  exact IsOpen.mem_nhds isOpen_univ (mem_univ 0)

variable [Nonempty ι]

theorem basisSets_smul (U) (hU : U ∈ p.basisSets) :
    ∃ V ∈ 𝓝 (0 : 𝕜), ∃ W ∈ p.addGroupFilterBasis.sets, V • W ⊆ U := by
  rcases p.basisSets_iff.mp hU with ⟨s, r, hr, hU⟩
  refine ⟨Metric.ball 0 √r, Metric.ball_mem_nhds 0 (Real.sqrt_pos.mpr hr), ?_⟩
  refine ⟨(s.sup p).ball 0 √r, p.basisSets_mem s (Real.sqrt_pos.mpr hr), ?_⟩
  refine Set.Subset.trans (ball_smul_ball (s.sup p) √r √r) ?_
  rw [hU, Real.mul_self_sqrt (le_of_lt hr)]

theorem basisSets_smul_left (x : 𝕜) (U : Set E) (hU : U ∈ p.basisSets) :
    ∃ V ∈ p.addGroupFilterBasis.sets, V ⊆ (fun y : E => x • y) ⁻¹' U := by
  rcases p.basisSets_iff.mp hU with ⟨s, r, hr, hU⟩
  rw [hU]
  by_cases h : x ≠ 0
  · rw [(s.sup p).smul_ball_preimage 0 r x h, smul_zero]
    use (s.sup p).ball 0 (r / ‖x‖)
    exact ⟨p.basisSets_mem s (div_pos hr (norm_pos_iff.mpr h)), Subset.rfl⟩
  refine ⟨(s.sup p).ball 0 r, p.basisSets_mem s hr, ?_⟩
  simp only [not_ne_iff.mp h, Set.subset_def, mem_ball_zero, hr, mem_univ, map_zero, imp_true_iff,
    preimage_const_of_mem, zero_smul]

protected def moduleFilterBasis : ModuleFilterBasis 𝕜 E where
  toAddGroupFilterBasis := p.addGroupFilterBasis
  smul' := p.basisSets_smul _
  smul_left' := p.basisSets_smul_left
  smul_right' := p.basisSets_smul_right

theorem filter_eq_iInf (p : SeminormFamily 𝕜 E ι) :
    p.moduleFilterBasis.toFilterBasis.filter = ⨅ i, (𝓝 0).comap (p i) := by
  refine le_antisymm (le_iInf fun i => ?_) ?_
  · rw [p.moduleFilterBasis.toFilterBasis.hasBasis.le_basis_iff
        (Metric.nhds_basis_ball.comap _)]
    intro ε hε
    refine ⟨(p i).ball 0 ε, ?_, ?_⟩
    · rw [← (Finset.sup_singleton : _ = p i)]
      exact p.basisSets_mem {i} hε
    · rw [id, (p i).ball_zero_eq_preimage_ball]
  · rw [p.moduleFilterBasis.toFilterBasis.hasBasis.ge_iff]
    rintro U (hU : U ∈ p.basisSets)
    rcases p.basisSets_iff.mp hU with ⟨s, r, hr, rfl⟩
    rw [id, Seminorm.ball_finset_sup_eq_iInter _ _ _ hr, s.iInter_mem_sets]
    exact fun i _ =>
      Filter.mem_iInf_of_mem i
        ⟨Metric.ball 0 r, Metric.ball_mem_nhds 0 hr,
          Eq.subset (p i).ball_zero_eq_preimage_ball.symm⟩

lemma basisSets_mem_nhds {𝕜 E ι : Type*} [NormedField 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] (p : SeminormFamily 𝕜 E ι)
    (hp : ∀ i, Continuous (p i)) (U : Set E) (hU : U ∈ p.basisSets) : U ∈ 𝓝 (0 : E) := by
  obtain ⟨s, r, hr, rfl⟩ := p.basisSets_iff.mp hU
  clear hU
  refine Seminorm.ball_mem_nhds ?_ hr
  classical
  induction s using Finset.induction_on
  case empty => simpa using continuous_zero
  case insert a s _ hs =>
    simp only [Finset.sup_insert, coe_sup]
    exact Continuous.max (hp a) hs

end SeminormFamily

end FilterBasis

section Bounded

namespace Seminorm

variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

variable [NormedField 𝕜₂] [AddCommGroup F] [Module 𝕜₂ F]

variable {σ₁₂ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ₁₂]

def IsBounded (p : ι → Seminorm 𝕜 E) (q : ι' → Seminorm 𝕜₂ F) (f : E →ₛₗ[σ₁₂] F) : Prop :=
  ∀ i, ∃ s : Finset ι, ∃ C : ℝ≥0, (q i).comp f ≤ C • s.sup p

theorem isBounded_const (ι' : Type*) [Nonempty ι'] {p : ι → Seminorm 𝕜 E} {q : Seminorm 𝕜₂ F}
    (f : E →ₛₗ[σ₁₂] F) :
    IsBounded p (fun _ : ι' => q) f ↔ ∃ (s : Finset ι) (C : ℝ≥0), q.comp f ≤ C • s.sup p := by
  simp only [IsBounded, forall_const]

theorem const_isBounded (ι : Type*) [Nonempty ι] {p : Seminorm 𝕜 E} {q : ι' → Seminorm 𝕜₂ F}
    (f : E →ₛₗ[σ₁₂] F) : IsBounded (fun _ : ι => p) q f ↔ ∀ i, ∃ C : ℝ≥0, (q i).comp f ≤ C • p := by
  constructor <;> intro h i
  · rcases h i with ⟨s, C, h⟩
    exact ⟨C, le_trans h (smul_le_smul (Finset.sup_le fun _ _ => le_rfl) le_rfl)⟩
  use {Classical.arbitrary ι}
  simp only [h, Finset.sup_singleton]

theorem isBounded_sup {p : ι → Seminorm 𝕜 E} {q : ι' → Seminorm 𝕜₂ F} {f : E →ₛₗ[σ₁₂] F}
    (hf : IsBounded p q f) (s' : Finset ι') :
    ∃ (C : ℝ≥0) (s : Finset ι), (s'.sup q).comp f ≤ C • s.sup p := by
  classical
    obtain rfl | _ := s'.eq_empty_or_nonempty
    · exact ⟨1, ∅, by simp [Seminorm.bot_eq_zero]⟩
    choose fₛ fC hf using hf
    use s'.card • s'.sup fC, Finset.biUnion s' fₛ
    have hs : ∀ i : ι', i ∈ s' → (q i).comp f ≤ s'.sup fC • (Finset.biUnion s' fₛ).sup p := by
      intro i hi
      refine (hf i).trans (smul_le_smul ?_ (Finset.le_sup hi))
      exact Finset.sup_mono (Finset.subset_biUnion_of_mem fₛ hi)
    refine (comp_mono f (finset_sup_le_sum q s')).trans ?_
    simp_rw [← pullback_apply, map_sum, pullback_apply]
    refine (Finset.sum_le_sum hs).trans ?_
    rw [Finset.sum_const, smul_assoc]

end Seminorm

end Bounded

section Topology

variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [Nonempty ι]

structure WithSeminorms (p : SeminormFamily 𝕜 E ι) [topology : TopologicalSpace E] : Prop where
  topology_eq_withSeminorms : topology = p.moduleFilterBasis.topology

theorem WithSeminorms.withSeminorms_eq {p : SeminormFamily 𝕜 E ι} [t : TopologicalSpace E]
    (hp : WithSeminorms p) : t = p.moduleFilterBasis.topology :=
  hp.1

variable [TopologicalSpace E]

variable {p : SeminormFamily 𝕜 E ι}

theorem WithSeminorms.topologicalAddGroup (hp : WithSeminorms p) : TopologicalAddGroup E := by
  rw [hp.withSeminorms_eq]
  exact AddGroupFilterBasis.isTopologicalAddGroup _

theorem WithSeminorms.continuousSMul (hp : WithSeminorms p) : ContinuousSMul 𝕜 E := by
  rw [hp.withSeminorms_eq]
  exact ModuleFilterBasis.continuousSMul _

theorem WithSeminorms.hasBasis (hp : WithSeminorms p) :
    (𝓝 (0 : E)).HasBasis (fun s : Set E => s ∈ p.basisSets) id := by
  rw [congr_fun (congr_arg (@nhds E) hp.1) 0]
  exact AddGroupFilterBasis.nhds_zero_hasBasis _

theorem WithSeminorms.hasBasis_zero_ball (hp : WithSeminorms p) :
    (𝓝 (0 : E)).HasBasis
    (fun sr : Finset ι × ℝ => 0 < sr.2) fun sr => (sr.1.sup p).ball 0 sr.2 := by
  refine ⟨fun V => ?_⟩
  simp only [hp.hasBasis.mem_iff, SeminormFamily.basisSets_iff, Prod.exists]
  constructor
  · rintro ⟨-, ⟨s, r, hr, rfl⟩, hV⟩
    exact ⟨s, r, hr, hV⟩
  · rintro ⟨s, r, hr, hV⟩
    exact ⟨_, ⟨s, r, hr, rfl⟩, hV⟩

theorem WithSeminorms.hasBasis_ball (hp : WithSeminorms p) {x : E} :
    (𝓝 (x : E)).HasBasis
    (fun sr : Finset ι × ℝ => 0 < sr.2) fun sr => (sr.1.sup p).ball x sr.2 := by
  have : TopologicalAddGroup E := hp.topologicalAddGroup
  rw [← map_add_left_nhds_zero]
  convert hp.hasBasis_zero_ball.map (x + ·) using 1
  ext sr : 1
  -- Porting note: extra type ascriptions needed on `0`
  have : (sr.fst.sup p).ball (x +ᵥ (0 : E)) sr.snd = x +ᵥ (sr.fst.sup p).ball 0 sr.snd :=
    Eq.symm (Seminorm.vadd_ball (sr.fst.sup p))
  rwa [vadd_eq_add, add_zero] at this

theorem WithSeminorms.mem_nhds_iff (hp : WithSeminorms p) (x : E) (U : Set E) :
    U ∈ 𝓝 x ↔ ∃ s : Finset ι, ∃ r > 0, (s.sup p).ball x r ⊆ U := by
  rw [hp.hasBasis_ball.mem_iff, Prod.exists]

theorem WithSeminorms.isOpen_iff_mem_balls (hp : WithSeminorms p) (U : Set E) :
    IsOpen U ↔ ∀ x ∈ U, ∃ s : Finset ι, ∃ r > 0, (s.sup p).ball x r ⊆ U := by
  simp_rw [← WithSeminorms.mem_nhds_iff hp _ U, isOpen_iff_mem_nhds]

-- DISSOLVED: WithSeminorms.T1_of_separating

-- DISSOLVED: WithSeminorms.separating_of_T1

-- DISSOLVED: WithSeminorms.separating_iff_T1

end Topology

section Tendsto

variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [Nonempty ι] [TopologicalSpace E]

variable {p : SeminormFamily 𝕜 E ι}

theorem WithSeminorms.tendsto_nhds' (hp : WithSeminorms p) (u : F → E) {f : Filter F} (y₀ : E) :
    Filter.Tendsto u f (𝓝 y₀) ↔
    ∀ (s : Finset ι) (ε), 0 < ε → ∀ᶠ x in f, s.sup p (u x - y₀) < ε := by
  simp [hp.hasBasis_ball.tendsto_right_iff]

theorem WithSeminorms.tendsto_nhds (hp : WithSeminorms p) (u : F → E) {f : Filter F} (y₀ : E) :
    Filter.Tendsto u f (𝓝 y₀) ↔ ∀ i ε, 0 < ε → ∀ᶠ x in f, p i (u x - y₀) < ε := by
  rw [hp.tendsto_nhds' u y₀]
  exact
    ⟨fun h i => by simpa only [Finset.sup_singleton] using h {i}, fun h s ε hε =>
      (s.eventually_all.2 fun i _ => h i ε hε).mono fun _ => finset_sup_apply_lt hε⟩

variable [SemilatticeSup F] [Nonempty F]

theorem WithSeminorms.tendsto_nhds_atTop (hp : WithSeminorms p) (u : F → E) (y₀ : E) :
    Filter.Tendsto u Filter.atTop (𝓝 y₀) ↔
    ∀ i ε, 0 < ε → ∃ x₀, ∀ x, x₀ ≤ x → p i (u x - y₀) < ε := by
  rw [hp.tendsto_nhds u y₀]
  exact forall₃_congr fun _ _ _ => Filter.eventually_atTop

end Tendsto

section TopologicalAddGroup

variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

variable [Nonempty ι]

section TopologicalSpace

variable [t : TopologicalSpace E]

theorem SeminormFamily.withSeminorms_of_nhds [TopologicalAddGroup E] (p : SeminormFamily 𝕜 E ι)
    (h : 𝓝 (0 : E) = p.moduleFilterBasis.toFilterBasis.filter) : WithSeminorms p := by
  refine
    ⟨TopologicalAddGroup.ext inferInstance p.addGroupFilterBasis.isTopologicalAddGroup ?_⟩
  rw [AddGroupFilterBasis.nhds_zero_eq]
  exact h

theorem SeminormFamily.withSeminorms_of_hasBasis [TopologicalAddGroup E] (p : SeminormFamily 𝕜 E ι)
    (h : (𝓝 (0 : E)).HasBasis (fun s : Set E => s ∈ p.basisSets) id) : WithSeminorms p :=
  p.withSeminorms_of_nhds <|
    Filter.HasBasis.eq_of_same_basis h p.addGroupFilterBasis.toFilterBasis.hasBasis

theorem SeminormFamily.withSeminorms_iff_nhds_eq_iInf [TopologicalAddGroup E]
    (p : SeminormFamily 𝕜 E ι) : WithSeminorms p ↔ (𝓝 (0 : E)) = ⨅ i, (𝓝 0).comap (p i) := by
  rw [← p.filter_eq_iInf]
  refine ⟨fun h => ?_, p.withSeminorms_of_nhds⟩
  rw [h.topology_eq_withSeminorms]
  exact AddGroupFilterBasis.nhds_zero_eq _

theorem SeminormFamily.withSeminorms_iff_topologicalSpace_eq_iInf [TopologicalAddGroup E]
    (p : SeminormFamily 𝕜 E ι) :
    WithSeminorms p ↔
      t = ⨅ i, (p i).toSeminormedAddCommGroup.toUniformSpace.toTopologicalSpace := by
  rw [p.withSeminorms_iff_nhds_eq_iInf,
    TopologicalAddGroup.ext_iff inferInstance (topologicalAddGroup_iInf fun i => inferInstance),
    nhds_iInf]
  congrm _ = ⨅ i, ?_
  exact @comap_norm_nhds_zero _ (p i).toSeminormedAddGroup

theorem WithSeminorms.continuous_seminorm {p : SeminormFamily 𝕜 E ι} (hp : WithSeminorms p)
    (i : ι) : Continuous (p i) := by
  have := hp.topologicalAddGroup
  rw [p.withSeminorms_iff_topologicalSpace_eq_iInf.mp hp]
  exact continuous_iInf_dom (@continuous_norm _ (p i).toSeminormedAddGroup)

end TopologicalSpace

theorem SeminormFamily.withSeminorms_iff_uniformSpace_eq_iInf [u : UniformSpace E]
    [UniformAddGroup E] (p : SeminormFamily 𝕜 E ι) :
    WithSeminorms p ↔ u = ⨅ i, (p i).toSeminormedAddCommGroup.toUniformSpace := by
  rw [p.withSeminorms_iff_nhds_eq_iInf,
    UniformAddGroup.ext_iff inferInstance (uniformAddGroup_iInf fun i => inferInstance),
    UniformSpace.toTopologicalSpace_iInf, nhds_iInf]
  congrm _ = ⨅ i, ?_
  exact @comap_norm_nhds_zero _ (p i).toAddGroupSeminorm.toSeminormedAddGroup

end TopologicalAddGroup

section NormedSpace

theorem norm_withSeminorms (𝕜 E) [NormedField 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] :
    WithSeminorms fun _ : Fin 1 => normSeminorm 𝕜 E := by
  let p : SeminormFamily 𝕜 E (Fin 1) := fun _ => normSeminorm 𝕜 E
  refine
    ⟨SeminormedAddCommGroup.toTopologicalAddGroup.ext
        p.addGroupFilterBasis.isTopologicalAddGroup ?_⟩
  refine Filter.HasBasis.eq_of_same_basis Metric.nhds_basis_ball ?_
  rw [← ball_normSeminorm 𝕜 E]
  refine
    Filter.HasBasis.to_hasBasis p.addGroupFilterBasis.nhds_zero_hasBasis ?_ fun r hr =>
      ⟨(normSeminorm 𝕜 E).ball 0 r, p.basisSets_singleton_mem 0 hr, rfl.subset⟩
  rintro U (hU : U ∈ p.basisSets)
  rcases p.basisSets_iff.mp hU with ⟨s, r, hr, hU⟩
  use r, hr
  rw [hU, id]
  by_cases h : s.Nonempty
  · rw [Finset.sup_const h]
  rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sup_empty, ball_bot _ hr]
  exact Set.subset_univ _

end NormedSpace

section NontriviallyNormedField

variable [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [Nonempty ι]

variable {p : SeminormFamily 𝕜 E ι}

variable [TopologicalSpace E]

theorem WithSeminorms.isVonNBounded_iff_finset_seminorm_bounded {s : Set E} (hp : WithSeminorms p) :
    Bornology.IsVonNBounded 𝕜 s ↔ ∀ I : Finset ι, ∃ r > 0, ∀ x ∈ s, I.sup p x < r := by
  rw [hp.hasBasis.isVonNBounded_iff]
  constructor
  · intro h I
    simp only [id] at h
    specialize h ((I.sup p).ball 0 1) (p.basisSets_mem I zero_lt_one)
    rcases h.exists_pos with ⟨r, hr, h⟩
    cases' NormedField.exists_lt_norm 𝕜 r with a ha
    specialize h a (le_of_lt ha)
    rw [Seminorm.smul_ball_zero (norm_pos_iff.1 <| hr.trans ha), mul_one] at h
    refine ⟨‖a‖, lt_trans hr ha, ?_⟩
    intro x hx
    specialize h hx
    exact (Finset.sup I p).mem_ball_zero.mp h
  intro h s' hs'
  rcases p.basisSets_iff.mp hs' with ⟨I, r, hr, hs'⟩
  rw [id, hs']
  rcases h I with ⟨r', _, h'⟩
  simp_rw [← (I.sup p).mem_ball_zero] at h'
  refine Absorbs.mono_right ?_ h'
  exact (Finset.sup I p).ball_zero_absorbs_ball_zero hr

theorem WithSeminorms.image_isVonNBounded_iff_finset_seminorm_bounded (f : G → E) {s : Set G}
    (hp : WithSeminorms p) :
    Bornology.IsVonNBounded 𝕜 (f '' s) ↔
      ∀ I : Finset ι, ∃ r > 0, ∀ x ∈ s, I.sup p (f x) < r := by
  simp_rw [hp.isVonNBounded_iff_finset_seminorm_bounded, Set.forall_mem_image]

theorem WithSeminorms.isVonNBounded_iff_seminorm_bounded {s : Set E} (hp : WithSeminorms p) :
    Bornology.IsVonNBounded 𝕜 s ↔ ∀ i : ι, ∃ r > 0, ∀ x ∈ s, p i x < r := by
  rw [hp.isVonNBounded_iff_finset_seminorm_bounded]
  constructor
  · intro hI i
    convert hI {i}
    rw [Finset.sup_singleton]
  intro hi I
  by_cases hI : I.Nonempty
  · choose r hr h using hi
    have h' : 0 < I.sup' hI r := by
      rcases hI with ⟨i, hi⟩
      exact lt_of_lt_of_le (hr i) (Finset.le_sup' r hi)
    refine ⟨I.sup' hI r, h', fun x hx => finset_sup_apply_lt h' fun i hi => ?_⟩
    refine lt_of_lt_of_le (h i x hx) ?_
    simp only [Finset.le_sup'_iff, exists_prop]
    exact ⟨i, hi, (Eq.refl _).le⟩
  simp only [Finset.not_nonempty_iff_eq_empty.mp hI, Finset.sup_empty, coe_bot, Pi.zero_apply,
    exists_prop]
  exact ⟨1, zero_lt_one, fun _ _ => zero_lt_one⟩

theorem WithSeminorms.image_isVonNBounded_iff_seminorm_bounded (f : G → E) {s : Set G}
    (hp : WithSeminorms p) :
    Bornology.IsVonNBounded 𝕜 (f '' s) ↔ ∀ i : ι, ∃ r > 0, ∀ x ∈ s, p i (f x) < r := by
  simp_rw [hp.isVonNBounded_iff_seminorm_bounded, Set.forall_mem_image]

end NontriviallyNormedField

section continuous_of_bounded

namespace Seminorm

variable [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

variable [NormedField 𝕝] [Module 𝕝 E]

variable [NontriviallyNormedField 𝕜₂] [AddCommGroup F] [Module 𝕜₂ F]

variable [NormedField 𝕝₂] [Module 𝕝₂ F]

variable {σ₁₂ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ₁₂]

variable {τ₁₂ : 𝕝 →+* 𝕝₂} [RingHomIsometric τ₁₂]

variable [Nonempty ι] [Nonempty ι']

theorem continuous_of_continuous_comp {q : SeminormFamily 𝕝₂ F ι'} [TopologicalSpace E]
    [TopologicalAddGroup E] [TopologicalSpace F] (hq : WithSeminorms q)
    (f : E →ₛₗ[τ₁₂] F) (hf : ∀ i, Continuous ((q i).comp f)) : Continuous f := by
  have : TopologicalAddGroup F := hq.topologicalAddGroup
  refine continuous_of_continuousAt_zero f ?_
  simp_rw [ContinuousAt, f.map_zero, q.withSeminorms_iff_nhds_eq_iInf.mp hq, Filter.tendsto_iInf,
    Filter.tendsto_comap_iff]
  intro i
  convert (hf i).continuousAt.tendsto
  exact (map_zero _).symm

theorem continuous_iff_continuous_comp {q : SeminormFamily 𝕜₂ F ι'} [TopologicalSpace E]
    [TopologicalAddGroup E] [TopologicalSpace F] (hq : WithSeminorms q) (f : E →ₛₗ[σ₁₂] F) :
    Continuous f ↔ ∀ i, Continuous ((q i).comp f) :=
    -- Porting note: if we *don't* use dot notation for `Continuous.comp`, Lean tries to show
    -- continuity of `((q i).comp f) ∘ id` because it doesn't see that `((q i).comp f)` is
    -- actually a composition of functions.
  ⟨fun h i => (hq.continuous_seminorm i).comp h, continuous_of_continuous_comp hq f⟩

theorem continuous_from_bounded {p : SeminormFamily 𝕝 E ι} {q : SeminormFamily 𝕝₂ F ι'}
    {_ : TopologicalSpace E} (hp : WithSeminorms p) {_ : TopologicalSpace F} (hq : WithSeminorms q)
    (f : E →ₛₗ[τ₁₂] F) (hf : Seminorm.IsBounded p q f) : Continuous f := by
  have : TopologicalAddGroup E := hp.topologicalAddGroup
  refine continuous_of_continuous_comp hq _ fun i => ?_
  rcases hf i with ⟨s, C, hC⟩
  rw [← Seminorm.finset_sup_smul] at hC
  -- Note: we deduce continuouty of `s.sup (C • p)` from that of `∑ i ∈ s, C • p i`.
  -- The reason is that there is no `continuous_finset_sup`, and even if it were we couldn't
  -- really use it since `ℝ` is not an `OrderBot`.
  refine Seminorm.continuous_of_le ?_ (hC.trans <| Seminorm.finset_sup_le_sum _ _)
  change Continuous (fun x ↦ Seminorm.coeFnAddMonoidHom _ _ (∑ i ∈ s, C • p i) x)
  simp_rw [map_sum, Finset.sum_apply]
  exact (continuous_finset_sum _ fun i _ ↦ (hp.continuous_seminorm i).const_smul (C : ℝ))

theorem cont_withSeminorms_normedSpace (F) [SeminormedAddCommGroup F] [NormedSpace 𝕝₂ F]
    [TopologicalSpace E] {p : ι → Seminorm 𝕝 E} (hp : WithSeminorms p)
    (f : E →ₛₗ[τ₁₂] F) (hf : ∃ (s : Finset ι) (C : ℝ≥0), (normSeminorm 𝕝₂ F).comp f ≤ C • s.sup p) :
    Continuous f := by
  rw [← Seminorm.isBounded_const (Fin 1)] at hf
  exact continuous_from_bounded hp (norm_withSeminorms 𝕝₂ F) f hf

theorem cont_normedSpace_to_withSeminorms (E) [SeminormedAddCommGroup E] [NormedSpace 𝕝 E]
    [TopologicalSpace F] {q : ι → Seminorm 𝕝₂ F} (hq : WithSeminorms q)
    (f : E →ₛₗ[τ₁₂] F) (hf : ∀ i : ι, ∃ C : ℝ≥0, (q i).comp f ≤ C • normSeminorm 𝕝 E) :
    Continuous f := by
  rw [← Seminorm.const_isBounded (Fin 1)] at hf
  exact continuous_from_bounded (norm_withSeminorms 𝕝 E) hq f hf

protected theorem _root_.WithSeminorms.equicontinuous_TFAE {κ : Type*}
    {q : SeminormFamily 𝕜₂ F ι'} [UniformSpace E] [UniformAddGroup E] [u : UniformSpace F]
    [hu : UniformAddGroup F] (hq : WithSeminorms q) [ContinuousSMul 𝕜 E]
    (f : κ → E →ₛₗ[σ₁₂] F) : TFAE
    [ EquicontinuousAt ((↑) ∘ f) 0,
      Equicontinuous ((↑) ∘ f),
      UniformEquicontinuous ((↑) ∘ f),
      ∀ i, ∃ p : Seminorm 𝕜 E, Continuous p ∧ ∀ k, (q i).comp (f k) ≤ p,
      ∀ i, BddAbove (range fun k ↦ (q i).comp (f k)) ∧ Continuous (⨆ k, (q i).comp (f k)) ] := by
  -- We start by reducing to the case where the target is a seminormed space
  rw [q.withSeminorms_iff_uniformSpace_eq_iInf.mp hq, uniformEquicontinuous_iInf_rng,
      equicontinuous_iInf_rng, equicontinuousAt_iInf_rng]
  refine forall_tfae [_, _, _, _, _] fun i ↦ ?_
  let _ : SeminormedAddCommGroup F := (q i).toSeminormedAddCommGroup
  clear u hu hq
  -- Now we can prove the equivalence in this setting
  simp only [List.map]
  tfae_have 1 → 3 := uniformEquicontinuous_of_equicontinuousAt_zero f
  tfae_have 3 → 2 := UniformEquicontinuous.equicontinuous
  tfae_have 2 → 1 := fun H ↦ H 0
  tfae_have 3 → 5
  | H => by
    have : ∀ᶠ x in 𝓝 0, ∀ k, q i (f k x) ≤ 1 := by
      filter_upwards [Metric.equicontinuousAt_iff_right.mp (H.equicontinuous 0) 1 one_pos]
        with x hx k
      simpa using (hx k).le
    have bdd : BddAbove (range fun k ↦ (q i).comp (f k)) :=
      Seminorm.bddAbove_of_absorbent (absorbent_nhds_zero this)
        (fun x hx ↦ ⟨1, forall_mem_range.mpr hx⟩)
    rw [← Seminorm.coe_iSup_eq bdd]
    refine ⟨bdd, Seminorm.continuous' (r := 1) ?_⟩
    filter_upwards [this] with x hx
    simpa only [closedBall_iSup bdd _ one_pos, mem_iInter, mem_closedBall_zero] using hx
  tfae_have 5 → 4 := fun H ↦ ⟨⨆ k, (q i).comp (f k), Seminorm.coe_iSup_eq H.1 ▸ H.2, le_ciSup H.1⟩
  tfae_have 4 → 1 -- This would work over any `NormedField`
  | ⟨p, hp, hfp⟩ =>
    Metric.equicontinuousAt_of_continuity_modulus p (map_zero p ▸ hp.tendsto 0) _ <|
      Eventually.of_forall fun x k ↦ by simpa using hfp k x
  tfae_finish

theorem _root_.WithSeminorms.uniformEquicontinuous_iff_exists_continuous_seminorm {κ : Type*}
    {q : SeminormFamily 𝕜₂ F ι'} [UniformSpace E] [UniformAddGroup E] [u : UniformSpace F]
    [UniformAddGroup F] (hq : WithSeminorms q) [ContinuousSMul 𝕜 E]
    (f : κ → E →ₛₗ[σ₁₂] F) :
    UniformEquicontinuous ((↑) ∘ f) ↔
    ∀ i, ∃ p : Seminorm 𝕜 E, Continuous p ∧ ∀ k, (q i).comp (f k) ≤ p :=
  (hq.equicontinuous_TFAE f).out 2 3

theorem _root_.WithSeminorms.uniformEquicontinuous_iff_bddAbove_and_continuous_iSup {κ : Type*}
    {q : SeminormFamily 𝕜₂ F ι'} [UniformSpace E] [UniformAddGroup E] [u : UniformSpace F]
    [UniformAddGroup F] (hq : WithSeminorms q) [ContinuousSMul 𝕜 E]
    (f : κ → E →ₛₗ[σ₁₂] F) :
    UniformEquicontinuous ((↑) ∘ f) ↔ ∀ i,
    BddAbove (range fun k ↦ (q i).comp (f k)) ∧
      Continuous (⨆ k, (q i).comp (f k)) :=
  (hq.equicontinuous_TFAE f).out 2 4

end Seminorm

section Congr

namespace WithSeminorms

variable [Nonempty ι] [Nonempty ι']

variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

variable [NormedField 𝕜₂] [AddCommGroup F] [Module 𝕜₂ F]

variable {σ₁₂ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ₁₂]

protected theorem congr {p : SeminormFamily 𝕜 E ι} {q : SeminormFamily 𝕜 E ι'}
    [t : TopologicalSpace E] (hp : WithSeminorms p) (hpq : Seminorm.IsBounded p q LinearMap.id)
    (hqp : Seminorm.IsBounded q p LinearMap.id) : WithSeminorms q := by
  constructor
  rw [hp.topology_eq_withSeminorms]
  clear hp t
  refine le_antisymm ?_ ?_ <;>
  rw [← continuous_id_iff_le] <;>
  refine continuous_from_bounded (.mk (topology := _) rfl) (.mk (topology := _) rfl)
    LinearMap.id (by assumption)

protected theorem finset_sups {p : SeminormFamily 𝕜 E ι} [TopologicalSpace E]
    (hp : WithSeminorms p) : WithSeminorms (fun s : Finset ι ↦ s.sup p) := by
  refine hp.congr ?_ ?_
  · intro s
    refine ⟨s, 1, ?_⟩
    rw [one_smul]
    rfl
  · intro i
    refine ⟨{{i}}, 1, ?_⟩
    rw [Finset.sup_singleton, Finset.sup_singleton, one_smul]
    rfl

protected theorem partial_sups [Preorder ι] [LocallyFiniteOrderBot ι] {p : SeminormFamily 𝕜 E ι}
    [TopologicalSpace E] (hp : WithSeminorms p) : WithSeminorms (fun i ↦ (Finset.Iic i).sup p) := by
  refine hp.congr ?_ ?_
  · intro i
    refine ⟨Finset.Iic i, 1, ?_⟩
    rw [one_smul]
    rfl
  · intro i
    refine ⟨{i}, 1, ?_⟩
    rw [Finset.sup_singleton, one_smul]
    exact (Finset.le_sup (Finset.mem_Iic.mpr le_rfl) : p i ≤ (Finset.Iic i).sup p)

protected theorem congr_equiv {p : SeminormFamily 𝕜 E ι} [t : TopologicalSpace E]
    (hp : WithSeminorms p) (e : ι' ≃ ι) : WithSeminorms (p ∘ e) := by
  refine hp.congr ?_ ?_ <;>
  intro i <;>
  [use {e i}, 1; use {e.symm i}, 1] <;>
  simp

end WithSeminorms

end Congr

end continuous_of_bounded

section bounded_of_continuous

namespace Seminorm

variable [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
  {p : SeminormFamily 𝕜 E ι}

lemma map_eq_zero_of_norm_zero (q : Seminorm 𝕜 F)
    (hq : Continuous q) {x : F} (hx : ‖x‖ = 0) : q x = 0 :=
  (map_zero q) ▸
    ((specializes_iff_mem_closure.mpr <| mem_closure_zero_iff_norm.mpr hx).map hq).eq.symm

lemma bound_of_continuous_normedSpace (q : Seminorm 𝕜 F)
    (hq : Continuous q) : ∃ C, 0 < C ∧ (∀ x : F, q x ≤ C * ‖x‖) := by
  have hq' : Tendsto q (𝓝 0) (𝓝 0) := map_zero q ▸ hq.tendsto 0
  rcases NormedAddCommGroup.nhds_zero_basis_norm_lt.mem_iff.mp (hq' <| Iio_mem_nhds one_pos)
    with ⟨ε, ε_pos, hε⟩
  rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc⟩
  have : 0 < ‖c‖ / ε := by positivity
  refine ⟨‖c‖ / ε, this, fun x ↦ ?_⟩
  by_cases hx : ‖x‖ = 0
  · rw [hx, mul_zero]
    exact le_of_eq (map_eq_zero_of_norm_zero q hq hx)
  · refine (normSeminorm 𝕜 F).bound_of_shell q ε_pos hc (fun x hle hlt ↦ ?_) hx
    refine (le_of_lt <| show q x < _ from hε hlt).trans ?_
    rwa [← div_le_iff₀' this, one_div_div]

-- DISSOLVED: bound_of_continuous

end Seminorm

end bounded_of_continuous

section LocallyConvexSpace

open LocallyConvexSpace

variable [Nonempty ι] [NormedField 𝕜] [NormedSpace ℝ 𝕜] [AddCommGroup E] [Module 𝕜 E] [Module ℝ E]
  [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E]

theorem WithSeminorms.toLocallyConvexSpace {p : SeminormFamily 𝕜 E ι} (hp : WithSeminorms p) :
    LocallyConvexSpace ℝ E := by
  have := hp.topologicalAddGroup
  apply ofBasisZero ℝ E id fun s => s ∈ p.basisSets
  · rw [hp.1, AddGroupFilterBasis.nhds_eq _, AddGroupFilterBasis.N_zero]
    exact FilterBasis.hasBasis _
  · intro s hs
    change s ∈ Set.iUnion _ at hs
    simp_rw [Set.mem_iUnion, Set.mem_singleton_iff] at hs
    rcases hs with ⟨I, r, _, rfl⟩
    exact convex_ball _ _ _

end LocallyConvexSpace

section NormedSpace

variable (𝕜) [NormedField 𝕜] [NormedSpace ℝ 𝕜] [SeminormedAddCommGroup E]

theorem NormedSpace.toLocallyConvexSpace' [NormedSpace 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] :
    LocallyConvexSpace ℝ E :=
  (norm_withSeminorms 𝕜 E).toLocallyConvexSpace

instance NormedSpace.toLocallyConvexSpace [NormedSpace ℝ E] : LocallyConvexSpace ℝ E :=
  NormedSpace.toLocallyConvexSpace' ℝ

end NormedSpace

section TopologicalConstructions

variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

variable [NormedField 𝕜₂] [AddCommGroup F] [Module 𝕜₂ F]

variable {σ₁₂ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ₁₂]

def SeminormFamily.comp (q : SeminormFamily 𝕜₂ F ι) (f : E →ₛₗ[σ₁₂] F) : SeminormFamily 𝕜 E ι :=
  fun i => (q i).comp f

theorem SeminormFamily.comp_apply (q : SeminormFamily 𝕜₂ F ι) (i : ι) (f : E →ₛₗ[σ₁₂] F) :
    q.comp f i = (q i).comp f :=
  rfl

theorem SeminormFamily.finset_sup_comp (q : SeminormFamily 𝕜₂ F ι) (s : Finset ι)
    (f : E →ₛₗ[σ₁₂] F) : (s.sup q).comp f = s.sup (q.comp f) := by
  ext x
  rw [Seminorm.comp_apply, Seminorm.finset_sup_apply, Seminorm.finset_sup_apply]
  rfl

variable [TopologicalSpace F]

theorem LinearMap.withSeminorms_induced [hι : Nonempty ι] {q : SeminormFamily 𝕜₂ F ι}
    (hq : WithSeminorms q) (f : E →ₛₗ[σ₁₂] F) :
    WithSeminorms (topology := induced f inferInstance) (q.comp f) := by
  have := hq.topologicalAddGroup
  let _ : TopologicalSpace E := induced f inferInstance
  have : TopologicalAddGroup E := topologicalAddGroup_induced f
  rw [(q.comp f).withSeminorms_iff_nhds_eq_iInf, nhds_induced, map_zero,
    q.withSeminorms_iff_nhds_eq_iInf.mp hq, Filter.comap_iInf]
  refine iInf_congr fun i => ?_
  exact Filter.comap_comap

lemma Topology.IsInducing.withSeminorms [hι : Nonempty ι] {q : SeminormFamily 𝕜₂ F ι}
    (hq : WithSeminorms q) [TopologicalSpace E] {f : E →ₛₗ[σ₁₂] F} (hf : IsInducing f) :
    WithSeminorms (q.comp f) := by
  rw [hf.eq_induced]
  exact f.withSeminorms_induced hq

protected def SeminormFamily.sigma {κ : ι → Type*} (p : (i : ι) → SeminormFamily 𝕜 E (κ i)) :
    SeminormFamily 𝕜 E ((i : ι) × κ i) :=
  fun ⟨i, k⟩ => p i k

theorem withSeminorms_iInf {κ : ι → Type*} [Nonempty ((i : ι) × κ i)] [∀ i, Nonempty (κ i)]
    {p : (i : ι) → SeminormFamily 𝕜 E (κ i)} {t : ι → TopologicalSpace E}
    (hp : ∀ i, WithSeminorms (topology := t i) (p i)) :
    WithSeminorms (topology := ⨅ i, t i) (SeminormFamily.sigma p) := by
  have : ∀ i, @TopologicalAddGroup E (t i) _ :=
    fun i ↦ @WithSeminorms.topologicalAddGroup _ _ _ _ _ _ _ (t i) _ (hp i)
  have : @TopologicalAddGroup E (⨅ i, t i) _ := topologicalAddGroup_iInf inferInstance
  simp_rw [@SeminormFamily.withSeminorms_iff_topologicalSpace_eq_iInf _ _ _ _ _ _ _ (_)] at hp ⊢
  rw [iInf_sigma]
  exact iInf_congr hp

theorem withSeminorms_pi {κ : ι → Type*} {E : ι → Type*}
    [∀ i, AddCommGroup (E i)] [∀ i, Module 𝕜 (E i)] [∀ i, TopologicalSpace (E i)]
    [Nonempty ((i : ι) × κ i)] [∀ i, Nonempty (κ i)] {p : (i : ι) → SeminormFamily 𝕜 (E i) (κ i)}
    (hp : ∀ i, WithSeminorms (p i)) :
    WithSeminorms (SeminormFamily.sigma (fun i ↦ (p i).comp (LinearMap.proj i))) :=
  withSeminorms_iInf fun i ↦ (LinearMap.proj i).withSeminorms_induced (hp i)

end TopologicalConstructions

section TopologicalProperties

variable [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [Nonempty ι] [Countable ι]

variable {p : SeminormFamily 𝕜 E ι}

variable [TopologicalSpace E]

theorem WithSeminorms.firstCountableTopology (hp : WithSeminorms p) :
    FirstCountableTopology E := by
  have := hp.topologicalAddGroup
  let _ : UniformSpace E := TopologicalAddGroup.toUniformSpace E
  have : UniformAddGroup E := comm_topologicalAddGroup_is_uniform
  have : (𝓝 (0 : E)).IsCountablyGenerated := by
    rw [p.withSeminorms_iff_nhds_eq_iInf.mp hp]
    exact Filter.iInf.isCountablyGenerated _
  have : (uniformity E).IsCountablyGenerated := UniformAddGroup.uniformity_countably_generated
  exact UniformSpace.firstCountableTopology E

WithSeminorms.first_countable := WithSeminorms.firstCountableTopology

end TopologicalProperties
