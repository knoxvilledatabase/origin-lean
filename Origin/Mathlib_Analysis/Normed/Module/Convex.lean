/-
Extracted from Analysis/Normed/Module/Convex.lean
Genuine: 15 of 15 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Metric properties of convex sets in normed spaces

We prove the following facts:

* `convexOn_norm`, `convexOn_dist` : norm and distance to a fixed point is convex on any convex
  set;
* `convexOn_univ_norm`, `convexOn_univ_dist` : norm and distance to a fixed point is convex on
  the whole space;
* `convexHull_ediam`, `convexHull_diam` : convex hull of a set has the same (e)metric diameter
  as the original set;
* `isBounded_convexHull` : convex hull of a set is bounded if and only if the original set
  is bounded.
-/

variable {E : Type*}

open Metric Set

section SeminormedAddCommGroup

variable [SeminormedAddCommGroup E] [NormedSpace ℝ E]

variable {s : Set E}

theorem convexOn_norm (hs : Convex ℝ s) : ConvexOn ℝ s norm :=
  ⟨hs, fun x _ y _ a b ha hb _ =>
    calc
      ‖a • x + b • y‖ ≤ ‖a • x‖ + ‖b • y‖ := norm_add_le _ _
      _ = a * ‖x‖ + b * ‖y‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]⟩

theorem convexOn_univ_norm : ConvexOn ℝ univ (norm : E → ℝ) :=
  convexOn_norm convex_univ

theorem convexOn_dist (z : E) (hs : Convex ℝ s) : ConvexOn ℝ s fun z' => dist z' z := by
  simpa [dist_eq_norm, preimage_preimage] using
    (convexOn_norm (hs.translate (-z))).comp_affineMap (AffineMap.id ℝ E - AffineMap.const ℝ E z)

theorem convexOn_univ_dist (z : E) : ConvexOn ℝ univ fun z' => dist z' z :=
  convexOn_dist z convex_univ

theorem convex_ball (a : E) (r : ℝ) : Convex ℝ (ball a r) := by
  simpa only [ball, sep_univ] using (convexOn_univ_dist a).convex_lt r

theorem convex_eball (a : E) (r : ENNReal) : Convex ℝ (eball a r) := by
  cases r with
  | top => simp [convex_univ]
  | coe r => simp [eball_coe, convex_ball]

theorem convex_closedBall (a : E) (r : ℝ) : Convex ℝ (closedBall a r) := by
  simpa only [closedBall, sep_univ] using (convexOn_univ_dist a).convex_le r

theorem segment_subset_closedBall_left (x y : E) : segment ℝ x y ⊆ closedBall x (dist x y) :=
  (convex_closedBall x _).segment_subset (mem_closedBall_self dist_nonneg)
    (mem_closedBall.mpr (dist_comm y x ▸ le_refl _))

theorem segment_subset_closedBall_right (x y : E) :
    segment ℝ x y ⊆ closedBall y (dist x y) := by
  rw [segment_symm]
  exact dist_comm x y ▸ segment_subset_closedBall_left y x

theorem convex_closedEBall (a : E) (r : ENNReal) : Convex ℝ (closedEBall a r) := by
  cases r with
  | top => simp [convex_univ]
  | coe r => simp [closedEBall_coe, convex_closedBall]

open Pointwise in

theorem convexHull_sphere_eq_closedBall {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [Nontrivial F] (x : F) {r : ℝ} (hr : 0 ≤ r) :
    convexHull ℝ (sphere x r) = closedBall x r := by
  suffices convexHull ℝ (sphere (0 : F) r) = closedBall 0 r by
    rw [← add_zero x, ← vadd_eq_add, ← vadd_sphere, convexHull_vadd,
      this, vadd_closedBall_zero, vadd_eq_add, add_zero]
  refine subset_antisymm (convexHull_min sphere_subset_closedBall (convex_closedBall 0 r))
    (fun x h ↦ mem_convexHull_iff.mpr fun U hU_sub hU ↦ ?_)
  have zero_mem : (0 : F) ∈ U := by
    have _ : Invertible (2 : ℝ) := by use 2⁻¹ <;> grind
    obtain ⟨z, hz⟩ := NormedSpace.sphere_nonempty (E := F).mpr hr
    rw [← midpoint_self_neg (R := ℝ) (x := z)]
    exact Convex.midpoint_mem hU (hU_sub hz) <| hU_sub (by simp_all)
  by_cases hr₀ : r = 0
  · simp_all
  by_cases x_zero : x = 0
  · rwa [x_zero]
  set z := (r * ‖x‖⁻¹) • x with hz_def
  have hr₁ : r⁻¹ * ‖x‖ ≤ 1 := by
    simp only [mem_closedBall, dist_zero_right] at h
    grw [h, inv_mul_le_one]
  have hz : z ∈ U := by
    apply hU_sub
    simp_all [norm_smul]
  have := StarConvex.smul_mem (hU.starConvex zero_mem) hz (by positivity) hr₁
  rwa [hz_def, ← smul_assoc, smul_eq_mul, ← mul_assoc, mul_comm, mul_comm r⁻¹, mul_assoc _ r⁻¹,
    inv_mul_cancel₀ hr₀, mul_one, inv_mul_cancel₀ (by simp_all), one_smul] at this

theorem convexHull_exists_dist_ge {s : Set E} {x : E} (hx : x ∈ convexHull ℝ s) (y : E) :
    ∃ x' ∈ s, dist x y ≤ dist x' y :=
  (convexOn_dist y (convex_convexHull ℝ _)).exists_ge_of_mem_convexHull (subset_convexHull ..) hx

theorem Convex.thickening (hs : Convex ℝ s) (δ : ℝ) : Convex ℝ (thickening δ s) := by
  rw [← add_ball_zero]
  exact hs.add (convex_ball 0 _)

theorem Convex.cthickening (hs : Convex ℝ s) (δ : ℝ) : Convex ℝ (cthickening δ s) := by
  obtain hδ | hδ := le_total 0 δ
  · rw [cthickening_eq_iInter_thickening hδ]
    exact convex_iInter₂ fun _ _ => hs.thickening _
  · rw [cthickening_of_nonpos hδ]
    exact hs.closure

theorem convexHull_exists_dist_ge2 {s t : Set E} {x y : E} (hx : x ∈ convexHull ℝ s)
    (hy : y ∈ convexHull ℝ t) : ∃ x' ∈ s, ∃ y' ∈ t, dist x y ≤ dist x' y' := by
  rcases convexHull_exists_dist_ge hx y with ⟨x', hx', Hx'⟩
  rcases convexHull_exists_dist_ge hy x' with ⟨y', hy', Hy'⟩
  use x', hx', y', hy'
  exact le_trans Hx' (dist_comm y x' ▸ dist_comm y' x' ▸ Hy')
