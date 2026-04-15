/-
Extracted from Probability/Moments/SubGaussian.lean
Genuine: 7 of 11 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# Sub-Gaussian random variables

This presentation of sub-Gaussian random variables is inspired by section 2.5 of
[vershynin2018high]. Let `X` be a random variable. Consider the following five properties, in which
`Kᵢ` are positive reals,
* (i) for all `t ≥ 0`, `ℙ(|X| ≥ t) ≤ 2 * exp(-t^2 / K₁^2)`,
* (ii) for all `p : ℕ` with `1 ≤ p`, `𝔼[|X|^p]^(1/p) ≤ K₂ sqrt(p)`,
* (iii) for all `|t| ≤ 1/K₃`, `𝔼[exp (t^2 * X^2)] ≤ exp (K₃^2 * t^2)`,
* (iv) `𝔼[exp(X^2 / K₄)] ≤ 2`,
* (v) for all `t : ℝ`, `𝔼[exp (t * X)] ≤ exp (K₅ * t^2 / 2)`.

Properties (i) to (iv) are equivalent, in the sense that there exists a constant `C` such that
if `X` satisfies one of those properties with constant `K`, then it satisfies any other one with
constant at most `CK`.

If `𝔼[X] = 0` then properties (i)-(iv) are equivalent to (v) in that same sense.
Property (v) implies that `X` has expectation zero.

The name sub-Gaussian is used by various authors to refer to any one of (i)-(v). We will say that a
random variable has sub-Gaussian moment-generating function (mgf) with constant `K₅` to mean that
property (v) holds with that constant. The function `exp (K₅ * t^2 / 2)` which appears in
property (v) is the mgf of a Gaussian with variance `K₅`.
That property (v) is the most convenient one to work with if one wants to prove concentration
inequalities using Chernoff's method.

TODO: implement definitions for (i)-(iv) when it makes sense. For example the maximal constant `K₄`
such that (iv) is true is an Orlicz norm. Prove relations between those properties.

### Conditionally sub-Gaussian random variables and kernels

A related notion to sub-Gaussian random variables is that of conditionally sub-Gaussian random
variables. A random variable `X` is conditionally sub-Gaussian in the sense of (v) with respect to
a sigma-algebra `m` and a measure `μ` if for all `t : ℝ`, `exp (t * X)` is `μ`-integrable and
the conditional mgf of `X` conditioned on `m` is almost surely bounded by `exp (c * t^2 / 2)`
for some constant `c`.

As in other parts of Mathlib's probability library (notably the independence and conditional
independence definitions), we express both sub-Gaussian and conditionally sub-Gaussian properties
as special cases of a notion of sub-Gaussianity with respect to a kernel and a measure.

## Main definitions

* `Kernel.HasSubgaussianMGF`: a random variable `X` has a sub-Gaussian moment-generating function
  with parameter `c` with respect to a kernel `κ` and a measure `ν` if for `ν`-almost all `ω'`,
  for all `t : ℝ`, the moment-generating function of `X` with respect to `κ ω'` is bounded by
  `exp (c * t ^ 2 / 2)`.
* `HasCondSubgaussianMGF`: a random variable `X` has a conditionally sub-Gaussian moment-generating
  function with parameter `c` with respect to a sigma-algebra `m` and a measure `μ` if for all
  `t : ℝ`, `exp (t * X)` is `μ`-integrable and the moment-generating function of `X` conditioned
  on `m` is almost surely bounded by `exp (c * t ^ 2 / 2)` for all `t : ℝ`.
  The actual definition uses `Kernel.HasSubgaussianMGF`: `HasCondSubgaussianMGF` is defined as
  sub-Gaussian with respect to the conditional expectation kernel for `m` and the restriction of `μ`
  to the sigma-algebra `m`.
* `HasSubgaussianMGF`: a random variable `X` has a sub-Gaussian moment-generating function
  with parameter `c` with respect to a measure `μ` if for all `t : ℝ`, `exp (t * X)`
  is `μ`-integrable and the moment-generating function of `X` is bounded by `exp (c * t ^ 2 / 2)`
  for all `t : ℝ`.
  This is equivalent to `Kernel.HasSubgaussianMGF` with a constant kernel.
  See `HasSubgaussianMGF_iff_kernel`.

## Main statements

* `measure_sum_ge_le_of_iIndepFun`: Hoeffding's inequality for sums of independent sub-Gaussian
  random variables.
* `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`: Hoeffding's lemma for random variables with
  expectation zero.
* `measure_sum_ge_le_of_HasCondSubgaussianMGF`: the Azuma-Hoeffding inequality for sub-Gaussian
  random variables.

## Implementation notes

### Definition of `Kernel.HasSubgaussianMGF`

The definition of sub-Gaussian with respect to a kernel and a measure is the following:
```
structure Kernel.HasSubgaussianMGF (X : Ω → ℝ) (c : ℝ≥0)
    (κ : Kernel Ω' Ω) (ν : Measure Ω' := by volume_tac) : Prop where
  integrable_exp_mul : ∀ t, Integrable (fun ω ↦ exp (t * X ω)) (κ ∘ₘ ν)
  mgf_le : ∀ᵐ ω' ∂ν, ∀ t, mgf X (κ ω') t ≤ exp (c * t ^ 2 / 2)
```
An interesting point is that the integrability condition is not integrability of `exp (t * X)`
with respect to `κ ω'` for `ν`-almost all `ω'`, but integrability with respect to `κ ∘ₘ ν`.
This is a stronger condition, as the weaker one did not allow to prove interesting results about
the sum of two sub-Gaussian random variables.

For the conditional case, that integrability condition reduces to integrability of `exp (t * X)`
with respect to `μ`.

### Definition of `HasCondSubgaussianMGF`

We define `HasCondSubgaussianMGF` as a special case of `Kernel.HasSubgaussianMGF` with the
conditional expectation kernel for `m`, `condExpKernel μ m`, and the restriction of `μ` to `m`,
`μ.trim hm` (where `hm` states that `m` is a sub-sigma-algebra).
Note that `condExpKernel μ m ∘ₘ μ.trim hm = μ`. The definition is equivalent to the two
conditions
* for all `t`, `exp (t * X)` is `μ`-integrable,
* for `μ.trim hm`-almost all `ω`, for all `t`, the mgf with respect to the conditional
  distribution `condExpKernel μ m ω` is bounded by `exp (c * t ^ 2 / 2)`.

For any `t`, we can write the mgf of `X` with respect to the conditional expectation kernel as
a conditional expectation, `(μ.trim hm)`-almost surely:
`mgf X (condExpKernel μ m ·) t =ᵐ[μ.trim hm] μ[fun ω' ↦ exp (t * X ω') | m]`.

## References

* [R. Vershynin, *High-dimensional probability: An introduction with applications in data
  science*][vershynin2018high]

-/

open MeasureTheory Real

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

section Kernel

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {ν : Measure Ω'} {κ : Kernel Ω' Ω} {X : Ω → ℝ} {c : ℝ≥0}

/-! ### Sub-Gaussian with respect to a kernel and a measure -/

structure Kernel.HasSubgaussianMGF (X : Ω → ℝ) (c : ℝ≥0)
    (κ : Kernel Ω' Ω) (ν : Measure Ω' := by volume_tac) : Prop where
  integrable_exp_mul : ∀ t, Integrable (fun ω ↦ exp (t * X ω)) (κ ∘ₘ ν)
  mgf_le : ∀ᵐ ω' ∂ν, ∀ t, mgf X (κ ω') t ≤ exp (c * t ^ 2 / 2)

namespace Kernel.HasSubgaussianMGF

section BasicProperties

lemma ae_integrable_exp_mul (h : HasSubgaussianMGF X c κ ν) (t : ℝ) :
    ∀ᵐ ω' ∂ν, Integrable (fun y ↦ exp (t * X y)) (κ ω') :=
  Measure.ae_integrable_of_integrable_comp (h.integrable_exp_mul t)

lemma ae_forall_memLp_exp_mul (h : HasSubgaussianMGF X c κ ν) (p : ℝ≥0) :
    ∀ᵐ ω' ∂ν, ∀ t, MemLp (fun ω ↦ exp (t * X ω)) p (κ ω') := by
  filter_upwards [h.ae_forall_integrable_exp_mul] with ω' hi t
  constructor
  · exact (hi t).1
  · by_cases hp : p = 0
    · simp [hp]
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (mod_cast hp) (by simp),
      ENNReal.coe_toReal]
    have hf := (hi (p * t)).lintegral_lt_top
    convert hf using 3 with ω
    rw [enorm_eq_ofReal (by positivity), ENNReal.ofReal_rpow_of_nonneg (by positivity),
      ← exp_mul, mul_comm, ← mul_assoc]
    positivity

lemma memLp_exp_mul (h : HasSubgaussianMGF X c κ ν) (t : ℝ) (p : ℝ≥0) :
    MemLp (fun ω ↦ exp (t * X ω)) p (κ ∘ₘ ν) := by
  by_cases hp0 : p = 0
  · simpa [hp0] using (h.integrable_exp_mul t).1
  constructor
  · exact (h.integrable_exp_mul t).1
  · rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (mod_cast hp0) (by simp)]
    simp only [ENNReal.coe_toReal]
    have h' := (h.integrable_exp_mul (p * t)).2
    rw [hasFiniteIntegral_def] at h'
    convert h' using 3 with ω
    rw [enorm_eq_ofReal (by positivity), enorm_eq_ofReal (by positivity),
      ENNReal.ofReal_rpow_of_nonneg (by positivity), ← exp_mul, mul_comm, ← mul_assoc]
    positivity

lemma isFiniteMeasure (h : HasSubgaussianMGF X c κ ν) :
    ∀ᵐ ω' ∂ν, IsFiniteMeasure (κ ω') := by
  filter_upwards [h.ae_integrable_exp_mul 0, h.mgf_le] with ω' h h_mgf
  simpa [integrable_const_iff] using h

lemma measure_univ_le_one (h : HasSubgaussianMGF X c κ ν) :
    ∀ᵐ ω' ∂ν, κ ω' Set.univ ≤ 1 := by
  filter_upwards [h.isFiniteMeasure, h.mgf_le] with ω' h h_mgf
  suffices (κ ω').real Set.univ ≤ 1 by
    rwa [← ENNReal.ofReal_one, ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) zero_le_one]
  simpa [mgf] using h_mgf 0

end BasicProperties

protected lemma of_rat (h_int : ∀ t : ℝ, Integrable (fun ω ↦ exp (t * X ω)) (κ ∘ₘ ν))
    (h_mgf : ∀ q : ℚ, ∀ᵐ ω' ∂ν, mgf X (κ ω') q ≤ exp (c * q ^ 2 / 2)) :
    Kernel.HasSubgaussianMGF X c κ ν where
  integrable_exp_mul := h_int
  mgf_le := by
    rw [← ae_all_iff] at h_mgf
    have h_int : ∀ᵐ ω' ∂ν, ∀ t, Integrable (fun ω ↦ exp (t * X ω)) (κ ω') := by
      have h_int' (n : ℤ) := Measure.ae_integrable_of_integrable_comp (h_int n)
      rw [← ae_all_iff] at h_int'
      filter_upwards [h_int'] with ω' h_int t
      exact integrable_exp_mul_of_le_of_le (h_int _) (h_int _) (Int.floor_le t) (Int.le_ceil t)
    filter_upwards [h_mgf, h_int] with ω' h_mgf h_int t
    refine Rat.denseRange_cast.induction_on t ?_ h_mgf
    exact isClosed_le (continuous_mgf h_int) (by fun_prop)
