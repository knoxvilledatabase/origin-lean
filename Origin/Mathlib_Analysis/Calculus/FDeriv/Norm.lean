/-
Extracted from Analysis/Calculus/FDeriv/Norm.lean
Genuine: 12 of 17 | Dissolved: 5 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.LineDeriv.Basic

/-!
# Differentiability of the norm in a real normed vector space

This file provides basic results about the differentiability of the norm in a real vector space.
Most are of the following kind: if the norm has some differentiability property
(`DifferentiableAt`, `ContDiffAt`, `HasStrictFDerivAt`, `HasFDerivAt`) at `x`, then so it has
at `t • x` when `t ≠ 0`.

## Main statements

* `ContDiffAt.contDiffAt_norm_smul`: If the norm is continuously differentiable up to order `n`
  at `x`, then so it is at `t • x` when `t ≠ 0`.
* `differentiableAt_norm_smul`: If `t ≠ 0`, the norm is differentiable at `x` if and only if
  it is at `t • x`.
* `HasFDerivAt.hasFDerivAt_norm_smul`: If the norm has a Fréchet derivative `f` at `x` and `t ≠ 0`,
  then it has `(SignType t) • f` as a Fréchet derivative at `t · x`.
* `fderiv_norm_smul` : `fderiv ℝ (‖·‖) (t • x) = (SignType.sign t : ℝ) • (fderiv ℝ (‖·‖) x)`,
  this holds without any differentiability assumptions.
* `DifferentiableAt.fderiv_norm_self`: if the norm is differentiable at `x`,
  then `fderiv ℝ (‖·‖) x x = ‖x‖`.
* `norm_fderiv_norm`: if the norm is differentiable at `x` then the operator norm of its derivative
  is `1` (on a non trivial space).

## Tags

differentiability, norm

-/

open ContinuousLinearMap Filter NNReal Real Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {n : WithTop ℕ∞} {f : E →L[ℝ] ℝ} {x : E} {t : ℝ}

variable (E) in

theorem not_differentiableAt_norm_zero [Nontrivial E] :
    ¬DifferentiableAt ℝ (‖·‖) (0 : E) := by
  obtain ⟨x, hx⟩ := NormedSpace.exists_lt_norm ℝ E 0
  intro h
  have : DifferentiableAt ℝ (fun t : ℝ ↦ ‖t • x‖) 0 := DifferentiableAt.comp _ (by simpa) (by simp)
  have : DifferentiableAt ℝ (|·|) (0 : ℝ) := by
    simp_rw [norm_smul, norm_eq_abs] at this
    have aux : abs = fun t ↦ (1 / ‖x‖) * (|t| * ‖x‖) := by field_simp
    rw [aux]
    exact this.const_mul _
  exact not_differentiableAt_abs_zero this

-- DISSOLVED: ContDiffAt.contDiffAt_norm_smul

-- DISSOLVED: contDiffAt_norm_smul_iff

theorem ContDiffAt.contDiffAt_norm_of_smul (h : ContDiffAt ℝ n (‖·‖) (t • x)) :
    ContDiffAt ℝ n (‖·‖) x := by
  rcases eq_bot_or_bot_lt n with rfl | hn
  · apply contDiffAt_zero.2
    exact ⟨univ, univ_mem, continuous_norm.continuousOn⟩
  replace hn : 1 ≤ n := ENat.add_one_natCast_le_withTop_of_lt hn
  obtain rfl | ht := eq_or_ne t 0
  · by_cases hE : Nontrivial E
    · rw [zero_smul] at h
      exact (mt (ContDiffAt.differentiableAt · (mod_cast hn)))
        (not_differentiableAt_norm_zero E) h |>.elim
    · rw [not_nontrivial_iff_subsingleton] at hE
      rw [eq_const_of_subsingleton (‖·‖) 0]
      exact contDiffAt_const
  · exact contDiffAt_norm_smul_iff ht |>.2 h

-- DISSOLVED: HasStrictFDerivAt.hasStrictFDerivAt_norm_smul

theorem HasStrictFDerivAt.hasStrictDerivAt_norm_smul_neg
    (ht : t < 0) (h : HasStrictFDerivAt (‖·‖) f x) :
    HasStrictFDerivAt (‖·‖) (-f) (t • x) := by
  simpa [ht] using h.hasStrictFDerivAt_norm_smul ht.ne

theorem HasStrictFDerivAt.hasStrictDerivAt_norm_smul_pos
    (ht : 0 < t) (h : HasStrictFDerivAt (‖·‖) f x) :
    HasStrictFDerivAt (‖·‖) f (t • x) := by
  simpa [ht] using h.hasStrictFDerivAt_norm_smul ht.ne'

-- DISSOLVED: HasFDerivAt.hasFDerivAt_norm_smul

theorem HasFDerivAt.hasFDerivAt_norm_smul_neg
    (ht : t < 0) (h : HasFDerivAt (‖·‖) f x) :
    HasFDerivAt (‖·‖) (-f) (t • x) := by
  simpa [ht] using h.hasFDerivAt_norm_smul ht.ne

theorem HasFDerivAt.hasFDerivAt_norm_smul_pos
    (ht : 0 < t) (h : HasFDerivAt (‖·‖) f x) :
    HasFDerivAt (‖·‖) f (t • x) := by
  simpa [ht] using h.hasFDerivAt_norm_smul ht.ne'

-- DISSOLVED: differentiableAt_norm_smul

theorem DifferentiableAt.differentiableAt_norm_of_smul (h : DifferentiableAt ℝ (‖·‖) (t • x)) :
    DifferentiableAt ℝ (‖·‖) x := by
  obtain rfl | ht := eq_or_ne t 0
  · by_cases hE : Nontrivial E
    · rw [zero_smul] at h
      exact not_differentiableAt_norm_zero E h |>.elim
    · rw [not_nontrivial_iff_subsingleton] at hE
      exact (hasFDerivAt_of_subsingleton _ _).differentiableAt
  · exact differentiableAt_norm_smul ht |>.2 h

theorem DifferentiableAt.fderiv_norm_self {x : E} (h : DifferentiableAt ℝ (‖·‖) x) :
    fderiv ℝ (‖·‖) x x = ‖x‖ := by
  rw [← h.lineDeriv_eq_fderiv, lineDeriv]
  have this (t : ℝ) : ‖x + t • x‖ = |1 + t| * ‖x‖ := by
    rw [← norm_eq_abs, ← norm_smul, add_smul, one_smul]
  simp_rw [this]
  rw [deriv_mul_const]
  · conv_lhs => enter [1, 1]; change _root_.abs ∘ (fun t ↦ 1 + t)
    rw [deriv_comp, deriv_abs, deriv_const_add]
    · simp
    · exact differentiableAt_abs (by norm_num)
    · exact differentiableAt_id.const_add _
  · exact (differentiableAt_abs (by norm_num)).comp _ (differentiableAt_id.const_add _)

variable (x t) in

theorem fderiv_norm_smul :
    fderiv ℝ (‖·‖) (t • x) = (SignType.sign t : ℝ) • (fderiv ℝ (‖·‖) x) := by
  by_cases hE : Nontrivial E
  · by_cases hd : DifferentiableAt ℝ (‖·‖) x
    · obtain rfl | ht := eq_or_ne t 0
      · simp only [zero_smul, _root_.sign_zero, SignType.coe_zero]
        exact fderiv_zero_of_not_differentiableAt <| not_differentiableAt_norm_zero E
      · rw [(hd.hasFDerivAt.hasFDerivAt_norm_smul ht).fderiv]
    · rw [fderiv_zero_of_not_differentiableAt hd, fderiv_zero_of_not_differentiableAt]
      · simp
      · exact mt DifferentiableAt.differentiableAt_norm_of_smul hd
  · rw [not_nontrivial_iff_subsingleton] at hE
    simp_rw [(hasFDerivAt_of_subsingleton _ _).fderiv, smul_zero]

theorem fderiv_norm_smul_pos (ht : 0 < t) :
    fderiv ℝ (‖·‖) (t • x) = fderiv ℝ (‖·‖) x := by
  simp [fderiv_norm_smul, ht]

theorem fderiv_norm_smul_neg (ht : t < 0) :
    fderiv ℝ (‖·‖) (t • x) = -fderiv ℝ (‖·‖) x := by
  simp [fderiv_norm_smul, ht]

theorem norm_fderiv_norm [Nontrivial E] (h : DifferentiableAt ℝ (‖·‖) x) :
    ‖fderiv ℝ (‖·‖) x‖ = 1 := by
  have : x ≠ 0 := fun hx ↦ not_differentiableAt_norm_zero E (hx ▸ h)
  refine le_antisymm (NNReal.coe_one ▸ norm_fderiv_le_of_lipschitz ℝ lipschitzWith_one_norm) ?_
  apply le_of_mul_le_mul_right _ (norm_pos_iff.2 this)
  calc
    1 * ‖x‖ = fderiv ℝ (‖·‖) x x := by rw [one_mul, h.fderiv_norm_self]
    _ ≤ ‖fderiv ℝ (‖·‖) x x‖ := le_norm_self _
    _ ≤ ‖fderiv ℝ (‖·‖) x‖ * ‖x‖ := le_opNorm _ _
