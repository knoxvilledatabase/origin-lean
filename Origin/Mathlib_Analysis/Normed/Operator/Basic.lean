/-
Extracted from Analysis/Normed/Operator/Basic.lean
Genuine: 5 of 5 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Operator norm on the space of continuous linear maps

Define the operator (semi)-norm on the space of continuous (semi)linear maps between (semi)-normed
spaces, and prove its basic properties. In particular, show that this space is itself a semi-normed
space.

Since a lot of elementary properties don't require `‖x‖ = 0 → x = 0` we start setting up the
theory for `SeminormedAddCommGroup`. Later we will specialize to `NormedAddCommGroup` in the
file `NormedSpace.lean`.

Note that most of statements that apply to semilinear maps only hold when the ring homomorphism
is isometric, as expressed by the typeclass `[RingHomIsometric σ]`.

## Main Results
* `ball_subset_range_iff_surjective` (and its variants) shows that a semi-linear map between normed
  spaces is surjective if and only if it contains a ball.

-/

suppress_compilation

open Bornology Metric

open Filter hiding map_smul

open scoped NNReal Topology Uniformity

variable {𝕜 𝕜₂ 𝕜₃ E F Fₗ G 𝓕 : Type*}

section SemiNormed

variable [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] [SeminormedAddCommGroup Fₗ]
  [SeminormedAddCommGroup G]

variable [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] [NontriviallyNormedField 𝕜₃]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] [NormedSpace 𝕜 Fₗ] [NormedSpace 𝕜₃ G]
  {σ₁₂ : 𝕜 →+* 𝕜₂} {σ₂₃ : 𝕜₂ →+* 𝕜₃} {σ₁₃ : 𝕜 →+* 𝕜₃} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

variable [FunLike 𝓕 E F]

variable [SemilinearMapClass 𝓕 σ₁₂ E F]

theorem ball_zero_subset_range_iff_surjective [RingHomSurjective σ₁₂] {f : 𝓕} {r : ℝ}
    (hr : 0 < r) : ball 0 r ⊆ Set.range f ↔ (⇑f).Surjective :=
  absorbent_ball (by simpa) |>.subset_range_iff_surjective (f := (f : E →ₛₗ[σ₁₂] F))

theorem ball_subset_range_iff_surjective [RingHomSurjective σ₁₂] {f : 𝓕} {x : F} {r : ℝ}
    (hr : 0 < r) : ball x r ⊆ Set.range f ↔ (⇑f).Surjective := by
  refine ⟨fun h ↦ ?_, by simp_all⟩
  rw [← ball_zero_subset_range_iff_surjective hr, ← LinearMap.coe_coe]
  simp_rw [← LinearMap.coe_range, Set.subset_def, SetLike.mem_coe] at h ⊢
  intro _ _
  rw [← Submodule.add_mem_iff_left (f : E →ₛₗ[σ₁₂] F).range (h _ <| mem_ball_self hr)]
  apply h
  simp_all

theorem closedBall_subset_range_iff_surjective [RingHomSurjective σ₁₂] {f : 𝓕} (x : F) {r : ℝ}
    (hr : 0 < r) : closedBall (x : F) r ⊆ Set.range f ↔ (⇑f).Surjective :=
  ⟨fun h ↦ (ball_subset_range_iff_surjective hr).mp <| subset_trans ball_subset_closedBall h,
    by simp_all⟩

variable {F' 𝓕' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F'] [Nontrivial F']

{τ : 𝕜 →+* ℝ} [FunLike 𝓕' E F'] [SemilinearMapClass 𝓕' τ E F']

theorem sphere_subset_range_iff_surjective [RingHomSurjective τ] {f : 𝓕'} {x : F'} {r : ℝ}
    (hr : 0 < r) : sphere x r ⊆ Set.range f ↔ (⇑f).Surjective := by
  refine ⟨fun h ↦ ?_, by simp_all⟩
  grw [← (closedBall_subset_range_iff_surjective x hr), ← convexHull_sphere_eq_closedBall x hr.le,
    convexHull_mono h, (convexHull_eq_self (𝕜 := ℝ) (s := Set.range ↑f)).mpr]
  exact Submodule.Convex.semilinear_range (E := F') (F' := E) (σ := τ) f

end

theorem norm_image_of_norm_eq_zero [SemilinearMapClass 𝓕 σ₁₂ E F] (f : 𝓕) (hf : Continuous f)
    {x : E} (hx : ‖x‖ = 0) : ‖f x‖ = 0 := by
  rw [← mem_closure_zero_iff_norm, ← specializes_iff_mem_closure, ← map_zero f] at *
  exact hx.map hf
