/-
Extracted from NumberTheory/EulerProduct/DirichletLSeries.lean
Genuine: 15 | Conflates: 0 | Dissolved: 1 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.NumberTheory.EulerProduct.ExpLog
import Mathlib.NumberTheory.LSeries.Dirichlet

noncomputable section

/-!
# The Euler Product for the Riemann Zeta Function and Dirichlet L-Series

The first main result of this file is the Euler Product formula for the Riemann ζ function
$$\prod_p \frac{1}{1 - p^{-s}}
   = \lim_{n \to \infty} \prod_{p < n} \frac{1}{1 - p^{-s}} = \zeta(s)$$
for $s$ with real part $> 1$ ($p$ runs through the primes).
`riemannZeta_eulerProduct` is the second equality above. There are versions
`riemannZeta_eulerProduct_hasProd` and `riemannZeta_eulerProduct_tprod` in terms of `HasProd`
and `tprod`, respectively.

The second result is `dirichletLSeries_eulerProduct` (with variants
`dirichletLSeries_eulerProduct_hasProd` and `dirichletLSeries_eulerProduct_tprod`),
which is the analogous statement for Dirichlet L-series.
-/

open Complex

variable {s : ℂ}

noncomputable
def riemannZetaSummandHom (hs : s ≠ 0) : ℕ →*₀ ℂ where
  toFun n := (n : ℂ) ^ (-s)
  map_zero' := by simp [hs]
  map_one' := by simp
  map_mul' m n := by
    simpa only [Nat.cast_mul, ofReal_natCast]
      using mul_cpow_ofReal_nonneg m.cast_nonneg n.cast_nonneg _

noncomputable
def dirichletSummandHom {n : ℕ} (χ : DirichletCharacter ℂ n) (hs : s ≠ 0) : ℕ →*₀ ℂ where
  toFun n := χ n * (n : ℂ) ^ (-s)
  map_zero' := by simp [hs]
  map_one' := by simp
  map_mul' m n := by
    simp_rw [← ofReal_natCast]
    simpa only [Nat.cast_mul, IsUnit.mul_iff, not_and, map_mul, ofReal_mul,
      mul_cpow_ofReal_nonneg m.cast_nonneg n.cast_nonneg _]
      using mul_mul_mul_comm ..

lemma summable_riemannZetaSummand (hs : 1 < s.re) :
    Summable (fun n ↦ ‖riemannZetaSummandHom (ne_zero_of_one_lt_re hs) n‖) := by
  simp only [riemannZetaSummandHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
  convert Real.summable_nat_rpow_inv.mpr hs with n
  rw [← ofReal_natCast, Complex.norm_eq_abs,
    abs_cpow_eq_rpow_re_of_nonneg (Nat.cast_nonneg n) <| re_neg_ne_zero_of_one_lt_re hs,
    neg_re, Real.rpow_neg <| Nat.cast_nonneg n]

lemma tsum_riemannZetaSummand (hs : 1 < s.re) :
    ∑' (n : ℕ), riemannZetaSummandHom (ne_zero_of_one_lt_re hs) n = riemannZeta s := by
  have hsum := summable_riemannZetaSummand hs
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs, tsum_eq_zero_add hsum.of_norm, map_zero, zero_add]
  simp only [riemannZetaSummandHom, cpow_neg, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk,
    Nat.cast_add, Nat.cast_one, one_div]

lemma summable_dirichletSummand {N : ℕ} (χ : DirichletCharacter ℂ N) (hs : 1 < s.re) :
    Summable (fun n ↦ ‖dirichletSummandHom χ (ne_zero_of_one_lt_re hs) n‖) := by
  simp only [dirichletSummandHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, norm_mul]
  exact (summable_riemannZetaSummand hs).of_nonneg_of_le (fun _ ↦ by positivity)
    (fun n ↦ mul_le_of_le_one_left (norm_nonneg _) <| χ.norm_le_one n)

open scoped LSeries.notation in

lemma tsum_dirichletSummand {N : ℕ} (χ : DirichletCharacter ℂ N) (hs : 1 < s.re) :
    ∑' (n : ℕ), dirichletSummandHom χ (ne_zero_of_one_lt_re hs) n = L ↗χ s := by
  simp only [dirichletSummandHom, cpow_neg, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, LSeries,
    LSeries.term_of_ne_zero' (ne_zero_of_one_lt_re hs), div_eq_mul_inv]

open Filter Nat Topology EulerProduct

theorem riemannZeta_eulerProduct_hasProd (hs : 1 < s.re) :
    HasProd (fun p : Primes ↦ (1 - (p : ℂ) ^ (-s))⁻¹) (riemannZeta s) := by
  rw [← tsum_riemannZetaSummand hs]
  apply eulerProduct_completely_multiplicative_hasProd <| summable_riemannZetaSummand hs

theorem riemannZeta_eulerProduct_tprod (hs : 1 < s.re) :
    ∏' p : Primes, (1 - (p : ℂ) ^ (-s))⁻¹ = riemannZeta s :=
  (riemannZeta_eulerProduct_hasProd hs).tprod_eq

theorem riemannZeta_eulerProduct (hs : 1 < s.re) :
    Tendsto (fun n : ℕ ↦ ∏ p ∈ primesBelow n, (1 - (p : ℂ) ^ (-s))⁻¹) atTop
      (𝓝 (riemannZeta s)) := by
  rw [← tsum_riemannZetaSummand hs]
  apply eulerProduct_completely_multiplicative <| summable_riemannZetaSummand hs

open scoped LSeries.notation

theorem DirichletCharacter.LSeries_eulerProduct_hasProd {N : ℕ} (χ : DirichletCharacter ℂ N)
    (hs : 1 < s.re) :
    HasProd (fun p : Primes ↦ (1 - χ p * (p : ℂ) ^ (-s))⁻¹) (L ↗χ s) := by
  rw [← tsum_dirichletSummand χ hs]
  convert eulerProduct_completely_multiplicative_hasProd <| summable_dirichletSummand χ hs

theorem DirichletCharacter.LSeries_eulerProduct_tprod {N : ℕ} (χ : DirichletCharacter ℂ N)
    (hs : 1 < s.re) :
    ∏' p : Primes, (1 - χ p * (p : ℂ) ^ (-s))⁻¹ = L ↗χ s :=
  (DirichletCharacter.LSeries_eulerProduct_hasProd χ hs).tprod_eq

theorem DirichletCharacter.LSeries_eulerProduct {N : ℕ} (χ : DirichletCharacter ℂ N)
    (hs : 1 < s.re) :
    Tendsto (fun n : ℕ ↦ ∏ p ∈ primesBelow n, (1 - χ p * (p : ℂ) ^ (-s))⁻¹) atTop
      (𝓝 (L ↗χ s)) := by
  rw [← tsum_dirichletSummand χ hs]
  apply eulerProduct_completely_multiplicative <| summable_dirichletSummand χ hs

open LSeries

theorem DirichletCharacter.LSeries_eulerProduct_exp_log {N : ℕ} (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 1 < s.re) :
    exp (∑' p : Nat.Primes, -log (1 - χ p * p ^ (-s))) = L ↗χ s := by
  let f := dirichletSummandHom χ <| ne_zero_of_one_lt_re hs
  have h n : term ↗χ s n = f n := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp only [term_zero, map_zero]
    · simp only [ne_eq, hn, not_false_eq_true, term_of_ne_zero, div_eq_mul_inv,
        dirichletSummandHom, cpow_neg, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, f]
  simpa only [LSeries, h]
    using exp_tsum_primes_log_eq_tsum (f := f) <| summable_dirichletSummand χ hs

open DirichletCharacter

theorem ArithmeticFunction.LSeries_zeta_eulerProduct_exp_log {s : ℂ} (hs : 1 < s.re) :
    exp (∑' p : Nat.Primes, -Complex.log (1 - p ^ (-s))) = L 1 s := by
  convert modOne_eq_one (R := ℂ) ▸
    DirichletCharacter.LSeries_eulerProduct_exp_log (1 : DirichletCharacter ℂ 1) hs using 7
  rw [MulChar.one_apply <| isUnit_of_subsingleton _, one_mul]

theorem riemannZeta_eulerProduct_exp_log {s : ℂ} (hs : 1 < s.re) :
    exp (∑' p : Nat.Primes, -Complex.log (1 - p ^ (-s))) = riemannZeta s :=
  LSeries_one_eq_riemannZeta hs ▸ ArithmeticFunction.LSeries_zeta_eulerProduct_exp_log hs

/-!
### Changing the level of a Dirichlet `L`-series
-/

-- DISSOLVED: DirichletCharacter.LSeries_changeLevel
