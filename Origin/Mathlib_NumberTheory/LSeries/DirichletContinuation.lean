/-
Extracted from NumberTheory/LSeries/DirichletContinuation.lean
Genuine: 21 | Conflates: 0 | Dissolved: 10 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.NumberTheory.LSeries.ZMod
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

/-!
# Analytic continuation of Dirichlet L-functions

We show that if `χ` is a Dirichlet character `ZMod N → ℂ`, for a positive integer `N`, then the
L-series of `χ` has analytic continuation (away from a pole at `s = 1` if `χ` is trivial), and
similarly for completed L-functions.

All definitions and theorems are in the `DirichletCharacter` namespace.

## Main definitions

* `LFunction χ s`: the L-function, defined as a linear combination of Hurwitz zeta functions.
* `completedLFunction χ s`: the completed L-function, which for *almost* all `s` is equal to
  `LFunction χ s * gammaFactor χ s` where `gammaFactor χ s` is the archimedean Gamma-factor.
* `rootNumber`: the global root number of the L-series of `χ` (for `χ` primitive; junk otherwise).

## Main theorems

* `LFunction_eq_LSeries`: if `1 < re s` then the `LFunction` coincides with the naive `LSeries`.
* `differentiable_LFunction`: if `χ` is nontrivial then `LFunction χ s` is differentiable
  everywhere.
* `LFunction_eq_completed_div_gammaFactor`: we have
  `LFunction χ s = completedLFunction χ s / gammaFactor χ s`, unless `s = 0` and `χ` is the trivial
  character modulo 1.
* `differentiable_completedLFunction`: if `χ` is nontrivial then `completedLFunction χ s` is
  differentiable everywhere.
* `IsPrimitive.completedLFunction_one_sub`: the **functional equation** for Dirichlet L-functions,
  showing that if `χ` is primitive modulo `N`, then
  `completedLFunction χ s = N ^ (s - 1 / 2) * rootNumber χ * completedLFunction χ⁻¹ s`.
-/

open HurwitzZeta Complex Finset Classical ZMod Filter

open scoped Real Topology

namespace DirichletCharacter

variable {N : ℕ} [NeZero N]

@[pp_nodot]
noncomputable def LFunction (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ := ZMod.LFunction χ s

@[simp] lemma LFunction_modOne_eq {χ : DirichletCharacter ℂ 1} :
    LFunction χ = riemannZeta := by
  ext; rw [LFunction, ZMod.LFunction_modOne_eq, (by rfl : (0 : ZMod 1) = 1), map_one, one_mul]

lemma LFunction_eq_LSeries (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < re s) :
    LFunction χ s = LSeries (χ ·) s :=
  ZMod.LFunction_eq_LSeries χ hs

lemma deriv_LFunction_eq_deriv_LSeries (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    deriv (LFunction χ) s = deriv (LSeries (χ ·)) s := by
  refine Filter.EventuallyEq.deriv_eq ?_
  have h : {z | 1 < z.re} ∈ nhds s :=
    (isOpen_lt continuous_const continuous_re).mem_nhds hs
  filter_upwards [h] with z hz
  exact LFunction_eq_LSeries χ hz

@[fun_prop]
lemma differentiableAt_LFunction (χ : DirichletCharacter ℂ N) (s : ℂ) (hs : s ≠ 1 ∨ χ ≠ 1) :
    DifferentiableAt ℂ (LFunction χ) s :=
  ZMod.differentiableAt_LFunction χ s (hs.imp_right χ.sum_eq_zero_of_ne_one)

@[fun_prop]
lemma differentiable_LFunction {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    Differentiable ℂ (LFunction χ) :=
  (differentiableAt_LFunction _ · <| Or.inr hχ)

@[simp]
lemma Even.LFunction_neg_two_mul_nat_add_one {χ : DirichletCharacter ℂ N} (hχ : Even χ) (n : ℕ) :
    LFunction χ (-(2 * (n + 1))) = 0 :=
  ZMod.LFunction_neg_two_mul_nat_add_one hχ.to_fun n

-- DISSOLVED: Even.LFunction_neg_two_mul_nat

@[simp] lemma Odd.LFunction_neg_two_mul_nat_sub_one
  {χ : DirichletCharacter ℂ N} (hχ : Odd χ) (n : ℕ) :
    LFunction χ (-(2 * n) - 1) = 0 :=
  ZMod.LFunction_neg_two_mul_nat_sub_one hχ.to_fun n

/-!
### Results on changing levels
-/

-- DISSOLVED: LFunction_changeLevel_aux

-- DISSOLVED: LFunction_changeLevel

/-!
### The `L`-function of the trivial character mod `N`
-/

-- DISSOLVED: LFunctionTrivChar

lemma LFunctionTrivChar_eq_mul_riemannZeta {s : ℂ} (hs : s ≠ 1) :
    LFunctionTrivChar N s = (∏ p ∈ N.primeFactors, (1 - (p : ℂ) ^ (-s))) * riemannZeta s := by
  rw [← LFunction_modOne_eq (χ := 1), LFunctionTrivChar, ← changeLevel_one N.one_dvd, mul_comm]
  convert LFunction_changeLevel N.one_dvd 1 (.inr hs) using 4 with p
  rw [MulChar.one_apply <| isUnit_of_subsingleton _, one_mul]

lemma LFunctionTrivChar_residue_one :
    Tendsto (fun s ↦ (s - 1) * LFunctionTrivChar N s) (𝓝[≠] 1)
      (𝓝 <| ∏ p ∈ N.primeFactors, (1 - (p : ℂ)⁻¹)) := by
  have H : (fun s ↦ (s - 1) * LFunctionTrivChar N s) =ᶠ[𝓝[≠] 1]
        fun s ↦ (∏ p ∈ N.primeFactors, (1 - (p : ℂ) ^ (-s))) * ((s - 1) * riemannZeta s) := by
    refine Set.EqOn.eventuallyEq_nhdsWithin fun s hs ↦ ?_
    rw [mul_left_comm, LFunctionTrivChar_eq_mul_riemannZeta hs]
  rw [tendsto_congr' H]
  conv => enter [3, 1]; rw [← mul_one <| Finset.prod ..]; enter [1, 2, p]; rw [← cpow_neg_one]
  refine .mul (f := fun s ↦ ∏ p ∈ N.primeFactors, _) ?_ riemannZeta_residue_one
  refine tendsto_nhdsWithin_of_tendsto_nhds <| Continuous.tendsto ?_ 1
  exact continuous_finset_prod _ fun p hp ↦ by
    have : NeZero p := ⟨(Nat.prime_of_mem_primeFactors hp).ne_zero⟩
    fun_prop

/-!
### Completed L-functions and the functional equation
-/

section gammaFactor

omit [NeZero N] -- not required for these declarations

noncomputable def gammaFactor (χ : DirichletCharacter ℂ N) (s : ℂ) :=
  if χ.Even then Gammaℝ s else Gammaℝ (s + 1)

lemma Even.gammaFactor_def {χ : DirichletCharacter ℂ N} (hχ : χ.Even) (s : ℂ) :
    gammaFactor χ s = Gammaℝ s := by
  simp only [gammaFactor, hχ, ↓reduceIte]

lemma Odd.gammaFactor_def {χ : DirichletCharacter ℂ N} (hχ : χ.Odd) (s : ℂ) :
    gammaFactor χ s = Gammaℝ (s + 1) := by
  simp only [gammaFactor, hχ.not_even, ↓reduceIte]

end gammaFactor

@[pp_nodot] noncomputable def completedLFunction (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  ZMod.completedLFunction χ s

lemma completedLFunction_modOne_eq {χ : DirichletCharacter ℂ 1} :
    completedLFunction χ = completedRiemannZeta := by
  ext; rw [completedLFunction, ZMod.completedLFunction_modOne_eq, map_one, one_mul]

-- DISSOLVED: differentiableAt_completedLFunction

lemma differentiable_completedLFunction {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    Differentiable ℂ (completedLFunction χ) := by
  refine fun s ↦ differentiableAt_completedLFunction _ _ (Or.inr ?_) (Or.inr hχ)
  exact hχ ∘ level_one' _

-- DISSOLVED: LFunction_eq_completed_div_gammaFactor

noncomputable def rootNumber (χ : DirichletCharacter ℂ N) : ℂ :=
  gaussSum χ stdAddChar / I ^ (if χ.Even then 0 else 1) / N ^ (1 / 2 : ℂ)

lemma rootNumber_modOne (χ : DirichletCharacter ℂ 1) : rootNumber χ = 1 := by
  simp only [rootNumber, gaussSum, ← singleton_eq_univ (1 : ZMod 1), sum_singleton, map_one,
    (show stdAddChar (1 : ZMod 1) = 1 from AddChar.map_zero_eq_one _), one_mul,
    (show χ.Even from map_one _), ite_true, pow_zero, div_one, Nat.cast_one, one_cpow]

namespace IsPrimitive

theorem completedLFunction_one_sub {χ : DirichletCharacter ℂ N} (hχ : IsPrimitive χ) (s : ℂ) :
    completedLFunction χ (1 - s) = N ^ (s - 1 / 2) * rootNumber χ * completedLFunction χ⁻¹ s := by
  -- First handle special case of Riemann zeta
  rcases eq_or_ne N 1 with rfl | hN
  · simp only [completedLFunction_modOne_eq, completedRiemannZeta_one_sub, Nat.cast_one, one_cpow,
      rootNumber_modOne, one_mul]
  -- facts about `χ` as function
  have h_sum : ∑ j, χ j = 0 := by
    refine χ.sum_eq_zero_of_ne_one (fun h ↦ hN.symm ?_)
    rwa [IsPrimitive, h, conductor_one (NeZero.ne _)] at hχ
  let ε := I ^ (if χ.Even then 0 else 1)
  -- gather up powers of N
  rw [rootNumber, ← mul_comm_div, ← mul_comm_div, ← cpow_sub _ _ (NeZero.ne _), sub_sub, add_halves]
  calc completedLFunction χ (1 - s)
  _ = N ^ (s - 1) * χ (-1) /  ε * ZMod.completedLFunction (𝓕 χ) s := by
    simp only [ε]
    split_ifs with h
    · rw [pow_zero, div_one, h, mul_one, completedLFunction,
        completedLFunction_one_sub_even h.to_fun _ (.inr h_sum) (.inr <| χ.map_zero' hN)]
    · replace h : χ.Odd := χ.even_or_odd.resolve_left h
      rw [completedLFunction, completedLFunction_one_sub_odd h.to_fun,
        pow_one, h, div_I, mul_neg_one, ← neg_mul, neg_neg]
  _ = (_) * ZMod.completedLFunction (fun j ↦ χ⁻¹ (-1) * gaussSum χ stdAddChar * χ⁻¹ j) s := by
    congr 2 with j
    rw [hχ.fourierTransform_eq_inv_mul_gaussSum, ← neg_one_mul j, map_mul, mul_right_comm]
  _ = N ^ (s - 1) / ε * gaussSum χ stdAddChar * completedLFunction χ⁻¹ s * (χ (-1) * χ⁻¹ (-1)):= by
    rw [completedLFunction, completedLFunction_const_mul]
    ring
  _ = N ^ (s - 1) / ε * gaussSum χ stdAddChar * completedLFunction χ⁻¹ s := by
    rw [← MulChar.mul_apply, mul_inv_cancel, MulChar.one_apply (isUnit_one.neg), mul_one]

end IsPrimitive

end DirichletCharacter

/-!
### The logarithmic derivative of the L-function of a Dirichlet character

We show that `s ↦ -(L' χ s) / L χ s + 1 / (s - 1)` is continuous outside the zeros of `L χ`
when `χ` is a trivial Dirichlet character and that `-L' χ / L χ` is continuous outside
the zeros of `L χ` when `χ` is nontrivial.
-/

namespace DirichletCharacter

open Complex

section trivial

variable (n : ℕ) [NeZero n]

noncomputable abbrev LFunctionTrivChar₁ : ℂ → ℂ :=
  Function.update (fun s ↦ (s - 1) * LFunctionTrivChar n s) 1
    (∏ p ∈ n.primeFactors, (1 - (p : ℂ)⁻¹))

-- DISSOLVED: LFunctionTrivChar₁_apply_one_ne_zero

lemma differentiable_LFunctionTrivChar₁ : Differentiable ℂ (LFunctionTrivChar₁ n) := by
  rw [← differentiableOn_univ,
    ← differentiableOn_compl_singleton_and_continuousAt_iff (c := 1) Filter.univ_mem]
  refine ⟨DifferentiableOn.congr (f := fun s ↦ (s - 1) * LFunctionTrivChar n s)
    (fun _ hs ↦ DifferentiableAt.differentiableWithinAt <| by fun_prop (disch := simp_all [hs]))
   fun _ hs ↦ Function.update_noteq (Set.mem_diff_singleton.mp hs).2 ..,
    continuousWithinAt_compl_self.mp ?_⟩
  simpa only [continuousWithinAt_compl_self, continuousAt_update_same]
    using LFunctionTrivChar_residue_one

-- DISSOLVED: deriv_LFunctionTrivChar₁_apply_of_ne_one

-- DISSOLVED: continuousOn_neg_logDeriv_LFunctionTrivChar₁

end trivial

section nontrivial

variable {n : ℕ} [NeZero n] {χ : DirichletCharacter ℂ n}

-- DISSOLVED: continuousOn_neg_logDeriv_LFunction_of_nontriv

end nontrivial

end DirichletCharacter
