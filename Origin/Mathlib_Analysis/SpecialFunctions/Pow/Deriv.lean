/-
Extracted from Analysis/SpecialFunctions/Pow/Deriv.lean
Genuine: 43 of 90 | Dissolved: 47 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Derivatives of power function on `ℂ`, `ℝ`, `ℝ≥0`, and `ℝ≥0∞`

We also prove differentiability and provide derivatives for the power functions `x ^ y`.
-/

noncomputable section

open scoped Real Topology NNReal ENNReal

open Filter

namespace Complex

theorem hasStrictFDerivAt_cpow {p : ℂ × ℂ} (hp : p.1 ∈ slitPlane) :
    HasStrictFDerivAt (fun x : ℂ × ℂ => x.1 ^ x.2)
      ((p.2 * p.1 ^ (p.2 - 1)) • ContinuousLinearMap.fst ℂ ℂ ℂ +
        (p.1 ^ p.2 * log p.1) • ContinuousLinearMap.snd ℂ ℂ ℂ) p := by
  have A : p.1 ≠ 0 := slitPlane_ne_zero hp
  have : (fun x : ℂ × ℂ => x.1 ^ x.2) =ᶠ[𝓝 p] fun x => exp (log x.1 * x.2) :=
    ((isOpen_ne.preimage continuous_fst).eventually_mem A).mono fun p hp =>
      cpow_def_of_ne_zero hp _
  rw [cpow_sub _ _ A, cpow_one, mul_div_left_comm, mul_smul, mul_smul]
  refine HasStrictFDerivAt.congr_of_eventuallyEq ?_ this.symm
  simpa only [cpow_def_of_ne_zero A, div_eq_mul_inv, mul_smul, add_comm, smul_add] using
    ((hasStrictFDerivAt_fst.clog hp).mul hasStrictFDerivAt_snd).cexp

theorem hasStrictFDerivAt_cpow' {x y : ℂ} (hp : x ∈ slitPlane) :
    HasStrictFDerivAt (fun x : ℂ × ℂ => x.1 ^ x.2)
      ((y * x ^ (y - 1)) • ContinuousLinearMap.fst ℂ ℂ ℂ +
        (x ^ y * log x) • ContinuousLinearMap.snd ℂ ℂ ℂ) (x, y) :=
  @hasStrictFDerivAt_cpow (x, y) hp

-- DISSOLVED: hasStrictDerivAt_const_cpow

theorem hasFDerivAt_cpow {p : ℂ × ℂ} (hp : p.1 ∈ slitPlane) :
    HasFDerivAt (fun x : ℂ × ℂ => x.1 ^ x.2)
      ((p.2 * p.1 ^ (p.2 - 1)) • ContinuousLinearMap.fst ℂ ℂ ℂ +
        (p.1 ^ p.2 * log p.1) • ContinuousLinearMap.snd ℂ ℂ ℂ) p :=
  (hasStrictFDerivAt_cpow hp).hasFDerivAt

end Complex

section fderiv

open Complex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : E → ℂ} {f' g' : E →L[ℂ] ℂ}
  {x : E} {s : Set E} {c : ℂ}

theorem HasStrictFDerivAt.cpow (hf : HasStrictFDerivAt f f' x) (hg : HasStrictFDerivAt g g' x)
    (h0 : f x ∈ slitPlane) : HasStrictFDerivAt (fun x => f x ^ g x)
      ((g x * f x ^ (g x - 1)) • f' + (f x ^ g x * Complex.log (f x)) • g') x := by
  convert (@hasStrictFDerivAt_cpow ((fun x => (f x, g x)) x) h0).comp x (hf.prod hg)

-- DISSOLVED: HasStrictFDerivAt.const_cpow

theorem HasFDerivAt.cpow (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x)
    (h0 : f x ∈ slitPlane) : HasFDerivAt (fun x => f x ^ g x)
      ((g x * f x ^ (g x - 1)) • f' + (f x ^ g x * Complex.log (f x)) • g') x := by
  convert (@Complex.hasFDerivAt_cpow ((fun x => (f x, g x)) x) h0).comp x (hf.prod hg)

-- DISSOLVED: HasFDerivAt.const_cpow

theorem HasFDerivWithinAt.cpow (hf : HasFDerivWithinAt f f' s x) (hg : HasFDerivWithinAt g g' s x)
    (h0 : f x ∈ slitPlane) : HasFDerivWithinAt (fun x => f x ^ g x)
      ((g x * f x ^ (g x - 1)) • f' + (f x ^ g x * Complex.log (f x)) • g') s x := by
  convert
    (@Complex.hasFDerivAt_cpow ((fun x => (f x, g x)) x) h0).comp_hasFDerivWithinAt x (hf.prod hg)

-- DISSOLVED: HasFDerivWithinAt.const_cpow

theorem DifferentiableAt.cpow (hf : DifferentiableAt ℂ f x) (hg : DifferentiableAt ℂ g x)
    (h0 : f x ∈ slitPlane) : DifferentiableAt ℂ (fun x => f x ^ g x) x :=
  (hf.hasFDerivAt.cpow hg.hasFDerivAt h0).differentiableAt

-- DISSOLVED: DifferentiableAt.const_cpow

theorem DifferentiableWithinAt.cpow (hf : DifferentiableWithinAt ℂ f s x)
    (hg : DifferentiableWithinAt ℂ g s x) (h0 : f x ∈ slitPlane) :
    DifferentiableWithinAt ℂ (fun x => f x ^ g x) s x :=
  (hf.hasFDerivWithinAt.cpow hg.hasFDerivWithinAt h0).differentiableWithinAt

-- DISSOLVED: DifferentiableWithinAt.const_cpow

theorem DifferentiableOn.cpow (hf : DifferentiableOn ℂ f s) (hg : DifferentiableOn ℂ g s)
    (h0 : Set.MapsTo f s slitPlane) : DifferentiableOn ℂ (fun x ↦ f x ^ g x) s :=
  fun x hx ↦ (hf x hx).cpow (hg x hx) (h0 hx)

-- DISSOLVED: DifferentiableOn.const_cpow

theorem Differentiable.cpow (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (h0 : ∀ x, f x ∈ slitPlane) : Differentiable ℂ (fun x ↦ f x ^ g x) :=
  fun x ↦ (hf x).cpow (hg x) (h0 x)

-- DISSOLVED: Differentiable.const_cpow

-- DISSOLVED: differentiable_const_cpow_of_neZero

-- DISSOLVED: differentiableAt_const_cpow_of_neZero

end fderiv

section deriv

open Complex

variable {f g : ℂ → ℂ} {s : Set ℂ} {f' g' x c : ℂ}

private theorem aux : ((g x * f x ^ (g x - 1)) • (1 : ℂ →L[ℂ] ℂ).smulRight f' +
    (f x ^ g x * log (f x)) • (1 : ℂ →L[ℂ] ℂ).smulRight g') 1 =
      g x * f x ^ (g x - 1) * f' + f x ^ g x * log (f x) * g' := by
  simp only [Algebra.id.smul_eq_mul, one_mul, ContinuousLinearMap.one_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.add_apply, Pi.smul_apply,
    ContinuousLinearMap.coe_smul']

nonrec theorem HasStrictDerivAt.cpow (hf : HasStrictDerivAt f f' x) (hg : HasStrictDerivAt g g' x)
    (h0 : f x ∈ slitPlane) : HasStrictDerivAt (fun x => f x ^ g x)
      (g x * f x ^ (g x - 1) * f' + f x ^ g x * Complex.log (f x) * g') x := by
  simpa using (hf.cpow hg h0).hasStrictDerivAt

-- DISSOLVED: HasStrictDerivAt.const_cpow

theorem Complex.hasStrictDerivAt_cpow_const (h : x ∈ slitPlane) :
    HasStrictDerivAt (fun z : ℂ => z ^ c) (c * x ^ (c - 1)) x := by
  simpa only [mul_zero, add_zero, mul_one] using
    (hasStrictDerivAt_id x).cpow (hasStrictDerivAt_const x c) h

theorem HasStrictDerivAt.cpow_const (hf : HasStrictDerivAt f f' x)
    (h0 : f x ∈ slitPlane) :
    HasStrictDerivAt (fun x => f x ^ c) (c * f x ^ (c - 1) * f') x :=
  (Complex.hasStrictDerivAt_cpow_const h0).comp x hf

theorem HasDerivAt.cpow (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x)
    (h0 : f x ∈ slitPlane) : HasDerivAt (fun x => f x ^ g x)
      (g x * f x ^ (g x - 1) * f' + f x ^ g x * Complex.log (f x) * g') x := by
  simpa only [aux] using (hf.hasFDerivAt.cpow hg h0).hasDerivAt

-- DISSOLVED: HasDerivAt.const_cpow

theorem HasDerivAt.cpow_const (hf : HasDerivAt f f' x) (h0 : f x ∈ slitPlane) :
    HasDerivAt (fun x => f x ^ c) (c * f x ^ (c - 1) * f') x :=
  (Complex.hasStrictDerivAt_cpow_const h0).hasDerivAt.comp x hf

theorem HasDerivWithinAt.cpow (hf : HasDerivWithinAt f f' s x) (hg : HasDerivWithinAt g g' s x)
    (h0 : f x ∈ slitPlane) : HasDerivWithinAt (fun x => f x ^ g x)
      (g x * f x ^ (g x - 1) * f' + f x ^ g x * Complex.log (f x) * g') s x := by
  simpa only [aux] using (hf.hasFDerivWithinAt.cpow hg h0).hasDerivWithinAt

-- DISSOLVED: HasDerivWithinAt.const_cpow

theorem HasDerivWithinAt.cpow_const (hf : HasDerivWithinAt f f' s x)
    (h0 : f x ∈ slitPlane) :
    HasDerivWithinAt (fun x => f x ^ c) (c * f x ^ (c - 1) * f') s x :=
  (Complex.hasStrictDerivAt_cpow_const h0).hasDerivAt.comp_hasDerivWithinAt x hf

-- DISSOLVED: hasDerivAt_ofReal_cpow

end deriv

namespace Real

variable {x y z : ℝ}

theorem hasStrictFDerivAt_rpow_of_pos (p : ℝ × ℝ) (hp : 0 < p.1) :
    HasStrictFDerivAt (fun x : ℝ × ℝ => x.1 ^ x.2)
      ((p.2 * p.1 ^ (p.2 - 1)) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (p.1 ^ p.2 * log p.1) • ContinuousLinearMap.snd ℝ ℝ ℝ) p := by
  have : (fun x : ℝ × ℝ => x.1 ^ x.2) =ᶠ[𝓝 p] fun x => exp (log x.1 * x.2) :=
    (continuousAt_fst.eventually (lt_mem_nhds hp)).mono fun p hp => rpow_def_of_pos hp _
  refine HasStrictFDerivAt.congr_of_eventuallyEq ?_ this.symm
  convert ((hasStrictFDerivAt_fst.log hp.ne').mul hasStrictFDerivAt_snd).exp using 1
  rw [rpow_sub_one hp.ne', ← rpow_def_of_pos hp, smul_add, smul_smul, mul_div_left_comm,
    div_eq_mul_inv, smul_smul, smul_smul, mul_assoc, add_comm]

theorem hasStrictFDerivAt_rpow_of_neg (p : ℝ × ℝ) (hp : p.1 < 0) :
    HasStrictFDerivAt (fun x : ℝ × ℝ => x.1 ^ x.2)
      ((p.2 * p.1 ^ (p.2 - 1)) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (p.1 ^ p.2 * log p.1 - exp (log p.1 * p.2) * sin (p.2 * π) * π) •
          ContinuousLinearMap.snd ℝ ℝ ℝ) p := by
  have : (fun x : ℝ × ℝ => x.1 ^ x.2) =ᶠ[𝓝 p] fun x => exp (log x.1 * x.2) * cos (x.2 * π) :=
    (continuousAt_fst.eventually (gt_mem_nhds hp)).mono fun p hp => rpow_def_of_neg hp _
  refine HasStrictFDerivAt.congr_of_eventuallyEq ?_ this.symm
  convert ((hasStrictFDerivAt_fst.log hp.ne).mul hasStrictFDerivAt_snd).exp.mul
    (hasStrictFDerivAt_snd.mul_const π).cos using 1
  simp_rw [rpow_sub_one hp.ne, smul_add, ← add_assoc, smul_smul, ← add_smul, ← mul_assoc,
    mul_comm (cos _), ← rpow_def_of_neg hp]
  rw [div_eq_mul_inv, add_comm]; congr 2 <;> ring

-- DISSOLVED: contDiffAt_rpow_of_ne

-- DISSOLVED: differentiableAt_rpow_of_ne

theorem _root_.HasStrictDerivAt.rpow {f g : ℝ → ℝ} {f' g' : ℝ} (hf : HasStrictDerivAt f f' x)
    (hg : HasStrictDerivAt g g' x) (h : 0 < f x) : HasStrictDerivAt (fun x => f x ^ g x)
      (f' * g x * f x ^ (g x - 1) + g' * f x ^ g x * Real.log (f x)) x := by
  convert (hasStrictFDerivAt_rpow_of_pos ((fun x => (f x, g x)) x) h).comp_hasStrictDerivAt x
    (hf.prod hg) using 1
  simp [mul_assoc, mul_comm, mul_left_comm]

-- DISSOLVED: hasStrictDerivAt_rpow_const_of_ne

theorem hasStrictDerivAt_const_rpow {a : ℝ} (ha : 0 < a) (x : ℝ) :
    HasStrictDerivAt (fun x => a ^ x) (a ^ x * log a) x := by
  simpa using (hasStrictDerivAt_const _ _).rpow (hasStrictDerivAt_id x) ha

-- DISSOLVED: differentiableAt_rpow_const_of_ne

lemma differentiableOn_rpow_const (p : ℝ) :
    DifferentiableOn ℝ (fun x => (x : ℝ) ^ p) {0}ᶜ :=
  fun _ hx => (Real.differentiableAt_rpow_const_of_ne p hx).differentiableWithinAt

theorem hasStrictDerivAt_const_rpow_of_neg {a x : ℝ} (ha : a < 0) :
    HasStrictDerivAt (fun x => a ^ x) (a ^ x * log a - exp (log a * x) * sin (x * π) * π) x := by
  simpa using (hasStrictFDerivAt_rpow_of_neg (a, x) ha).comp_hasStrictDerivAt x
    ((hasStrictDerivAt_const _ _).prod (hasStrictDerivAt_id _))

end Real

namespace Real

variable {z x y : ℝ}

-- DISSOLVED: hasDerivAt_rpow_const

theorem differentiable_rpow_const {p : ℝ} (hp : 1 ≤ p) : Differentiable ℝ fun x : ℝ => x ^ p :=
  fun _ => (hasDerivAt_rpow_const (Or.inr hp)).differentiableAt

-- DISSOLVED: deriv_rpow_const

theorem deriv_rpow_const' {p : ℝ} (h : 1 ≤ p) :
    (deriv fun x : ℝ => x ^ p) = fun x => p * x ^ (p - 1) :=
  funext fun _ => deriv_rpow_const (Or.inr h)

-- DISSOLVED: contDiffAt_rpow_const_of_ne

theorem contDiff_rpow_const_of_le {p : ℝ} {n : ℕ} (h : ↑n ≤ p) :
    ContDiff ℝ n fun x : ℝ => x ^ p := by
  induction' n with n ihn generalizing p
  · exact contDiff_zero.2 (continuous_id.rpow_const fun x => Or.inr <| by simpa using h)
  · have h1 : 1 ≤ p := le_trans (by simp) h
    rw [Nat.cast_succ, ← le_sub_iff_add_le] at h
    rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = n + 1 from rfl,
      contDiff_succ_iff_deriv, deriv_rpow_const' h1]
    simp only [WithTop.natCast_ne_top, analyticOn_univ, IsEmpty.forall_iff, true_and]
    exact ⟨differentiable_rpow_const h1, contDiff_const.mul (ihn h)⟩

theorem contDiffAt_rpow_const_of_le {x p : ℝ} {n : ℕ} (h : ↑n ≤ p) :
    ContDiffAt ℝ n (fun x : ℝ => x ^ p) x :=
  (contDiff_rpow_const_of_le h).contDiffAt

-- DISSOLVED: contDiffAt_rpow_const

-- DISSOLVED: hasStrictDerivAt_rpow_const

end Real

section Differentiability

open Real

section fderiv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f g : E → ℝ} {f' g' : E →L[ℝ] ℝ}
  {x : E} {s : Set E} {c p : ℝ} {n : WithTop ℕ∞}

theorem HasFDerivWithinAt.rpow (hf : HasFDerivWithinAt f f' s x) (hg : HasFDerivWithinAt g g' s x)
    (h : 0 < f x) : HasFDerivWithinAt (fun x => f x ^ g x)
      ((g x * f x ^ (g x - 1)) • f' + (f x ^ g x * Real.log (f x)) • g') s x := by
  exact (hasStrictFDerivAt_rpow_of_pos (f x, g x) h).hasFDerivAt.comp_hasFDerivWithinAt x
    (hf.prod hg)

theorem HasFDerivAt.rpow (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x) (h : 0 < f x) :
    HasFDerivAt (fun x => f x ^ g x)
      ((g x * f x ^ (g x - 1)) • f' + (f x ^ g x * Real.log (f x)) • g') x := by
  exact (hasStrictFDerivAt_rpow_of_pos (f x, g x) h).hasFDerivAt.comp x (hf.prod hg)

theorem HasStrictFDerivAt.rpow (hf : HasStrictFDerivAt f f' x) (hg : HasStrictFDerivAt g g' x)
    (h : 0 < f x) : HasStrictFDerivAt (fun x => f x ^ g x)
      ((g x * f x ^ (g x - 1)) • f' + (f x ^ g x * Real.log (f x)) • g') x :=
  (hasStrictFDerivAt_rpow_of_pos (f x, g x) h).comp x (hf.prod hg)

-- DISSOLVED: DifferentiableWithinAt.rpow

-- DISSOLVED: DifferentiableAt.rpow

-- DISSOLVED: DifferentiableOn.rpow

-- DISSOLVED: Differentiable.rpow

-- DISSOLVED: HasFDerivWithinAt.rpow_const

-- DISSOLVED: HasFDerivAt.rpow_const

-- DISSOLVED: HasStrictFDerivAt.rpow_const

-- DISSOLVED: DifferentiableWithinAt.rpow_const

-- DISSOLVED: DifferentiableAt.rpow_const

-- DISSOLVED: DifferentiableOn.rpow_const

-- DISSOLVED: Differentiable.rpow_const

theorem HasFDerivWithinAt.const_rpow (hf : HasFDerivWithinAt f f' s x) (hc : 0 < c) :
    HasFDerivWithinAt (fun x => c ^ f x) ((c ^ f x * Real.log c) • f') s x :=
  (hasStrictDerivAt_const_rpow hc (f x)).hasDerivAt.comp_hasFDerivWithinAt x hf

theorem HasFDerivAt.const_rpow (hf : HasFDerivAt f f' x) (hc : 0 < c) :
    HasFDerivAt (fun x => c ^ f x) ((c ^ f x * Real.log c) • f') x :=
  (hasStrictDerivAt_const_rpow hc (f x)).hasDerivAt.comp_hasFDerivAt x hf

theorem HasStrictFDerivAt.const_rpow (hf : HasStrictFDerivAt f f' x) (hc : 0 < c) :
    HasStrictFDerivAt (fun x => c ^ f x) ((c ^ f x * Real.log c) • f') x :=
  (hasStrictDerivAt_const_rpow hc (f x)).comp_hasStrictFDerivAt x hf

-- DISSOLVED: ContDiffWithinAt.rpow

-- DISSOLVED: ContDiffAt.rpow

-- DISSOLVED: ContDiffOn.rpow

-- DISSOLVED: ContDiff.rpow

-- DISSOLVED: ContDiffWithinAt.rpow_const_of_ne

-- DISSOLVED: ContDiffAt.rpow_const_of_ne

-- DISSOLVED: ContDiffOn.rpow_const_of_ne

-- DISSOLVED: ContDiff.rpow_const_of_ne

variable {m : ℕ}

theorem ContDiffWithinAt.rpow_const_of_le (hf : ContDiffWithinAt ℝ m f s x) (h : ↑m ≤ p) :
    ContDiffWithinAt ℝ m (fun x => f x ^ p) s x :=
  (contDiffAt_rpow_const_of_le h).comp_contDiffWithinAt x hf

theorem ContDiffAt.rpow_const_of_le (hf : ContDiffAt ℝ m f x) (h : ↑m ≤ p) :
    ContDiffAt ℝ m (fun x => f x ^ p) x := by
  rw [← contDiffWithinAt_univ] at *; exact hf.rpow_const_of_le h

theorem ContDiffOn.rpow_const_of_le (hf : ContDiffOn ℝ m f s) (h : ↑m ≤ p) :
    ContDiffOn ℝ m (fun x => f x ^ p) s := fun x hx => (hf x hx).rpow_const_of_le h

theorem ContDiff.rpow_const_of_le (hf : ContDiff ℝ m f) (h : ↑m ≤ p) :
    ContDiff ℝ m fun x => f x ^ p :=
  contDiff_iff_contDiffAt.mpr fun _ => hf.contDiffAt.rpow_const_of_le h

end fderiv

section deriv

variable {f g : ℝ → ℝ} {f' g' x y p : ℝ} {s : Set ℝ}

theorem HasDerivWithinAt.rpow (hf : HasDerivWithinAt f f' s x) (hg : HasDerivWithinAt g g' s x)
    (h : 0 < f x) : HasDerivWithinAt (fun x => f x ^ g x)
      (f' * g x * f x ^ (g x - 1) + g' * f x ^ g x * Real.log (f x)) s x := by
  convert (hf.hasFDerivWithinAt.rpow hg.hasFDerivWithinAt h).hasDerivWithinAt using 1
  dsimp; ring

theorem HasDerivAt.rpow (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) (h : 0 < f x) :
    HasDerivAt (fun x => f x ^ g x)
      (f' * g x * f x ^ (g x - 1) + g' * f x ^ g x * Real.log (f x)) x := by
  rw [← hasDerivWithinAt_univ] at *
  exact hf.rpow hg h

-- DISSOLVED: HasDerivWithinAt.rpow_const

-- DISSOLVED: HasDerivAt.rpow_const

-- DISSOLVED: derivWithin_rpow_const

-- DISSOLVED: deriv_rpow_const

-- DISSOLVED: isTheta_deriv_rpow_const_atTop

lemma isBigO_deriv_rpow_const_atTop (p : ℝ) :
    deriv (fun (x : ℝ) => x ^ p) =O[atTop] fun x => x ^ (p-1) := by
  rcases eq_or_ne p 0 with rfl | hp
  case inl =>
    simp [zero_sub, Real.rpow_neg_one, Real.rpow_zero, deriv_const', Asymptotics.isBigO_zero]
  case inr =>
    exact (isTheta_deriv_rpow_const_atTop hp).1

end deriv

end Differentiability

section Limits

open Real Filter

theorem tendsto_one_plus_div_rpow_exp (t : ℝ) :
    Tendsto (fun x : ℝ => (1 + t / x) ^ x) atTop (𝓝 (exp t)) := by
  apply ((Real.continuous_exp.tendsto _).comp (tendsto_mul_log_one_plus_div_atTop t)).congr' _
  have h₁ : (1 : ℝ) / 2 < 1 := by norm_num
  have h₂ : Tendsto (fun x : ℝ => 1 + t / x) atTop (𝓝 1) := by
    simpa using (tendsto_inv_atTop_zero.const_mul t).const_add 1
  refine (h₂.eventually_const_le h₁).mono fun x hx => ?_
  have hx' : 0 < 1 + t / x := by linarith
  simp [mul_comm x, exp_mul, exp_log hx']

theorem tendsto_one_plus_div_pow_exp (t : ℝ) :
    Tendsto (fun x : ℕ => (1 + t / (x : ℝ)) ^ x) atTop (𝓝 (Real.exp t)) :=
  ((tendsto_one_plus_div_rpow_exp t).comp tendsto_natCast_atTop_atTop).congr (by simp)

end Limits
