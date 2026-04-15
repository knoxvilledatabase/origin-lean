/-
Extracted from Analysis/Complex/OpenMapping.lean
Genuine: 7 of 14 | Dissolved: 4 | Infrastructure: 3
-/
import Origin.Core

/-!
# The open mapping theorem for holomorphic functions

This file proves the open mapping theorem for holomorphic functions, namely that an analytic
function on a preconnected set of the complex plane is either constant or open. The main step is to
show a local version of the theorem that states that if `f` is analytic at a point `z₀`, then either
it is constant in a neighborhood of `z₀` or it maps any neighborhood of `z₀` to a neighborhood of
its image `f z₀`. The results extend in higher dimension to `g : E → ℂ`.

The proof of the local version on `ℂ` goes through two main steps: first, assuming that the function
is not constant around `z₀`, use the isolated zero principle to show that `‖f z‖` is bounded below
on a small `sphere z₀ r` around `z₀`, and then use the maximum principle applied to the auxiliary
function `(fun z ↦ ‖f z - v‖)` to show that any `v` close enough to `f z₀` is in `f '' ball z₀ r`.
That second step is implemented in `DiffContOnCl.ball_subset_image_closedBall`.

## Main results

* `AnalyticAt.eventually_constant_or_nhds_le_map_nhds` is the local version of the open mapping
  theorem around a point;
* `AnalyticOnNhd.is_constant_or_isOpen` is the open mapping theorem on a connected open set.

As an immediate corollary, we show that a holomorphic function whose real part is constant is itself
constant.
-/

open Set Filter Metric Complex

open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {U : Set E} {f : ℂ → ℂ} {g : E → ℂ}
  {z₀ : ℂ} {ε r : ℝ}

theorem AnalyticAt.eventually_constant_or_nhds_le_map_nhds_aux (hf : AnalyticAt ℂ f z₀) :
    (∀ᶠ z in 𝓝 z₀, f z = f z₀) ∨ 𝓝 (f z₀) ≤ map f (𝓝 z₀) := by
  /- The function `f` is analytic in a neighborhood of `z₀`; by the isolated zeros principle, if `f`
    is not constant in a neighborhood of `z₀`, then it is nonzero, and therefore bounded below, on
    every small enough circle around `z₀` and then `DiffContOnCl.ball_subset_image_closedBall`
    provides an explicit ball centered at `f z₀` contained in the range of `f`. -/
  refine or_iff_not_imp_left.mpr fun h => ?_
  refine (nhds_basis_ball.le_basis_iff (nhds_basis_closedBall.map f)).mpr fun R hR => ?_
  have h1 := (hf.eventually_eq_or_eventually_ne analyticAt_const).resolve_left h
  have h2 : ∀ᶠ z in 𝓝 z₀, AnalyticAt ℂ f z := (isOpen_analyticAt ℂ f).eventually_mem hf
  obtain ⟨ρ, hρ, h3, h4⟩ :
    ∃ ρ > 0, AnalyticOnNhd ℂ f (closedBall z₀ ρ) ∧ ∀ z ∈ closedBall z₀ ρ, z ≠ z₀ → f z ≠ f z₀ := by
    simpa only [setOf_and, subset_inter_iff] using
      nhds_basis_closedBall.mem_iff.mp (h2.and (eventually_nhdsWithin_iff.mp h1))
  replace h3 : DiffContOnCl ℂ f (ball z₀ ρ) :=
    ⟨h3.differentiableOn.mono ball_subset_closedBall,
      (closure_ball z₀ hρ.lt.ne.symm).symm ▸ h3.continuousOn⟩
  let r := ρ ⊓ R
  have hr : 0 < r := lt_inf_iff.mpr ⟨hρ, hR⟩
  have h5 : closedBall z₀ r ⊆ closedBall z₀ ρ := closedBall_subset_closedBall inf_le_left
  have h6 : DiffContOnCl ℂ f (ball z₀ r) := h3.mono (ball_subset_ball inf_le_left)
  have h7 : ∀ z ∈ sphere z₀ r, f z ≠ f z₀ := fun z hz =>
    h4 z (h5 (sphere_subset_closedBall hz)) (ne_of_mem_sphere hz hr.ne.symm)
  have h8 : (sphere z₀ r).Nonempty := NormedSpace.sphere_nonempty.mpr hr.le
  have h9 : ContinuousOn (fun x => ‖f x - f z₀‖) (sphere z₀ r) := continuous_norm.comp_continuousOn
    ((h6.sub_const (f z₀)).continuousOn_ball.mono sphere_subset_closedBall)
  obtain ⟨x, hx, hfx⟩ := (isCompact_sphere z₀ r).exists_isMinOn h8 h9
  refine ⟨‖f x - f z₀‖ / 2, half_pos (norm_sub_pos_iff.mpr (h7 x hx)), ?_⟩
  exact (h6.ball_subset_image_closedBall hr (fun z hz => hfx hz) (not_eventually.mp h)).trans
    (by gcongr; exact inf_le_right)

theorem AnalyticOnNhd.is_constant_or_isOpenMap (hg : AnalyticOnNhd ℂ g .univ) :
    (∃ w, ∀ z, g z = w) ∨ IsOpenMap g :=
  (hg.is_constant_or_isOpen PreconnectedSpace.isPreconnected_univ).imp
    (fun ⟨w, eq⟩ ↦ ⟨w, fun z ↦ eq z ⟨⟩⟩) (· · <| subset_univ _)

/-!
## Holomorphic Functions with Constant Real or Imaginary Part
-/

theorem AnalyticOnNhd.eq_const_of_re_eq_const {U : Set ℂ} {c₀ : ℝ} (h₁f : AnalyticOnNhd ℂ f U)
    (h₂f : ∀ x ∈ U, (f x).re = c₀) (h₁U : IsOpen U) (h₂U : IsConnected U) :
    ∃ c, ∀ x ∈ U, f x = c := by
  obtain ⟨z₀, _⟩ := h₂U.nonempty
  by_contra h₅
  grind [not_isOpen_singleton (c₀ : ℝ), (by aesop : (re '' (f '' U)) = { c₀ }), isOpenMap_re
    (f '' U) ((h₁f.is_constant_or_isOpen h₂U.isPreconnected).resolve_left h₅ U (by tauto) h₁U)]

theorem AnalyticOnNhd.eq_re_add_const_mul_I_of_re_eq_const {U : Set ℂ} {c₀ : ℝ}
    (h₁f : AnalyticOnNhd ℂ f U) (h₂f : ∀ x ∈ U, (f x).re = c₀) (h₁U : IsOpen U)
    (h₂U : IsConnected U) :
    ∃ (c : ℝ), ∀ x ∈ U, f x = c₀ + c * I := by
  obtain ⟨cc, hcc⟩ := eq_const_of_re_eq_const h₁f h₂f h₁U h₂U
  use cc.im
  simp_rw [Complex.ext_iff]
  aesop

theorem AnalyticOnNhd.eq_const_of_im_eq_const {U : Set ℂ} {c₀ : ℝ} (h₁f : AnalyticOnNhd ℂ f U)
    (h₂f : ∀ x ∈ U, (f x).im = c₀) (h₁U : IsOpen U) (h₂U : IsConnected U) :
    ∃ c, ∀ x ∈ U, f x = c := by
  obtain ⟨z₀, _⟩ := h₂U.nonempty
  by_contra h₅
  grind [not_isOpen_singleton (c₀ : ℝ), (by aesop : (im '' (f '' U)) = { c₀ }), isOpenMap_im
    (f '' U) ((h₁f.is_constant_or_isOpen h₂U.isPreconnected).resolve_left h₅ U (by tauto) h₁U)]

theorem AnalyticOnNhd.eq_const_add_im_mul_I_of_re_eq_const {U : Set ℂ} {c₀ : ℝ}
    (h₁f : AnalyticOnNhd ℂ f U) (h₂f : ∀ x ∈ U, (f x).im = c₀) (h₁U : IsOpen U)
    (h₂U : IsConnected U) :
    ∃ (c : ℝ), ∀ x ∈ U, f x = c + c₀ * I := by
  obtain ⟨cc, hcc⟩ := AnalyticOnNhd.eq_const_of_im_eq_const h₁f h₂f h₁U h₂U
  use cc.re
  simp_rw [Complex.ext_iff]
  aesop

/-!
## Holomorphic Functions as Open Quotient Maps
-/

theorem Polynomial.C_eq_or_isOpenQuotientMap_eval (p : Polynomial ℂ) :
    (∃ x, C x = p) ∨ IsOpenQuotientMap p.eval := by
  refine or_iff_not_imp_left.mpr fun h ↦ ?_
  obtain ⟨x, eq⟩ | hp := (AnalyticOnNhd.eval_polynomial p).is_constant_or_isOpenMap
  · exact (h ⟨x, funext <| by simpa [eq_comm (a := x)]⟩).elim
  · exact ⟨IsAlgClosed.eval_surjective <| natDegree_eq_zero.not.mpr h, p.continuous_aeval, hp⟩

-- DISSOLVED: Polynomial.isOpenQuotientMap_eval

namespace Complex

-- DISSOLVED: isOpenQuotientMap_pow

-- DISSOLVED: isOpenQuotientMap_pow_compl_zero

-- DISSOLVED: isOpenQuotientMap_zpow_compl_zero

end Complex
