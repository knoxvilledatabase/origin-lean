/-
Extracted from Analysis/Meromorphic/FactorizedRational.lean
Genuine: 12 of 18 | Dissolved: 5 | Infrastructure: 1
-/
import Origin.Core

/-!
# Factorized Rational Functions

This file discusses functions `𝕜 → 𝕜` of the form `∏ᶠ u, (· - u) ^ d u`, where `d : 𝕜 → ℤ` is
integer-valued. We show that these "factorized rational functions" are meromorphic in normal form,
with divisor equal to `d`.

Under suitable assumptions, we show that meromorphic functions are equivalent, modulo equality on
codiscrete sets, to the product of a factorized rational function and an analytic function without
zeros.

Implementation Note: For consistency, we use `∏ᶠ u, (· - u) ^ d u` throughout. If the support of `d`
is finite, then evaluation of functions commutes with finprod, and the helper lemma
`Function.FactorizedRational.finprod_eval` asserts that `∏ᶠ u, (· - u) ^ d u` equals the function
`fun x ↦ ∏ᶠ u, (x - u) ^ d u`. If `d` has infinite support, this equality is wrong in general.
There are elementary examples of functions `d` where `∏ᶠ u, (· - u) ^ d u` is constant one, while
`fun x ↦ ∏ᶠ u, (x - u) ^ d u` is not continuous.
-/

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {U : Set 𝕜}

open Filter Function Real Set

namespace Function.FactorizedRational

/-!
## Elementary Properties of Factorized Rational Functions
-/

lemma mulSupport (d : 𝕜 → ℤ) :
    (fun u ↦ (· - u) ^ d u).mulSupport = d.support := by
  ext u
  constructor <;> intro h
  · simp_all only [mem_mulSupport, ne_eq, mem_support]
    by_contra hCon
    simp_all [zpow_zero]
  · simp_all only [mem_mulSupport, ne_eq, ne_iff]
    use u
    simp_all [zero_zpow_eq_one₀]

theorem analyticAt {d : 𝕜 → ℤ} {x : 𝕜} (h : 0 ≤ d x) :
    AnalyticAt 𝕜 (∏ᶠ u, (· - u) ^ d u) x := by
  apply analyticAt_finprod
  intro u
  by_cases h₂ : x = u
  · apply AnalyticAt.fun_zpow_nonneg (by fun_prop)
    rwa [← h₂]
  · apply AnalyticAt.fun_zpow (by fun_prop)
    rwa [sub_ne_zero]

-- DISSOLVED: ne_zero

open Classical in

lemma extractFactor {d : 𝕜 → ℤ} (u₀ : 𝕜) (hd : d.HasFiniteSupport) :
    (∏ᶠ u, (· - u) ^ d u) = ((· - u₀) ^ d u₀) * (∏ᶠ u, (· - u) ^ (update d u₀ 0 u)) := by
  by_cases h₁d : d u₀ = 0
  · simp [← eq_update_self_iff.2 h₁d, h₁d]
  · have : (fun u ↦ (fun x ↦ x - u) ^ d u).mulSupport ⊆ hd.toFinset := by
      simp [mulSupport]
    rw [finprod_eq_prod_of_mulSupport_subset _ this]
    have : u₀ ∈ hd.toFinset := by simp_all
    rw [← Finset.mul_prod_erase hd.toFinset _ this]
    congr 1
    have : (fun u ↦ (· - u) ^ (update d u₀ 0 u)).mulSupport ⊆ hd.toFinset.erase u₀ := by
      rw [mulSupport]
      intro x hx
      by_cases h₁x : x = u₀ <;> simp_all
    simp_all [finprod_eq_prod_of_mulSupport_subset _ this, Finset.prod_congr rfl]

theorem meromorphicNFOn_univ (d : 𝕜 → ℤ) :
    MeromorphicNFOn (∏ᶠ u, (· - u) ^ d u) univ := by
  classical
  by_cases hd : d.support.Finite
  · intro z hz
    rw [extractFactor z hd]
    right
    use d z, (∏ᶠ u, (· - u) ^ update d z 0 u)
    simp [analyticAt, ne_zero]
  · rw [← mulSupport d] at hd
    rw [finprod_of_infinite_mulSupport hd]
    exact AnalyticOnNhd.meromorphicNFOn analyticOnNhd_const

theorem meromorphicNFOn (d : 𝕜 → ℤ) (U : Set 𝕜) :
    MeromorphicNFOn (∏ᶠ u, (· - u) ^ d u) U := fun _ _ ↦ meromorphicNFOn_univ d (trivial)

/-!
## Orders and Divisors of Factorized Rational Functions
-/

theorem meromorphicOrderAt_eq {z : 𝕜} (d : 𝕜 → ℤ) (h₁d : d.HasFiniteSupport) :
    meromorphicOrderAt (∏ᶠ u, (· - u) ^ d u) z = d z := by
  classical
  rw [meromorphicOrderAt_eq_int_iff ((meromorphicNFOn_univ d).meromorphicOn _ (mem_univ _))]
  use ∏ᶠ u, (· - u) ^ update d z 0 u
  simp only [update_self, le_refl, analyticAt, ne_eq, ne_zero, not_false_eq_true, smul_eq_mul,
    true_and]
  filter_upwards
  simp [extractFactor z h₁d]

theorem meromorphicOrderAt_ne_top {z : 𝕜} (d : 𝕜 → ℤ) :
    meromorphicOrderAt (∏ᶠ u, (· - u) ^ d u) z ≠ ⊤ := by
  classical
  by_cases hd : d.support.Finite
  · simp [meromorphicOrderAt_eq d hd]
  · rw [← mulSupport] at hd
    simp [finprod_of_infinite_mulSupport hd]

theorem divisor {U : Set 𝕜} {D : locallyFinsuppWithin U ℤ} (hD : D.support.Finite) :
    MeromorphicOn.divisor (∏ᶠ u, (· - u) ^ D u) U = D := by
  ext z
  by_cases hz : z ∈ U
  <;> simp [(meromorphicNFOn D U).meromorphicOn, hz, meromorphicOrderAt_eq D hD]

open Classical in

private lemma mulSupport_update {d : 𝕜 → ℤ} {x : 𝕜}
    (h : d.support.Finite) :
    (fun u ↦ (x - u) ^ Function.update d x 0 u).mulSupport ⊆ h.toFinset := by
  intro u
  contrapose
  simp only [mem_mulSupport, ne_eq, Decidable.not_not]
  by_cases h₁ : u = x
  · rw [h₁]
    simp
  · simp_all

open Classical in

theorem meromorphicTrailingCoeffAt_factorizedRational {d : 𝕜 → ℤ} {x : 𝕜} (h : d.HasFiniteSupport) :
    meromorphicTrailingCoeffAt (∏ᶠ u, (· - u) ^ d u) x = ∏ᶠ u, (x - u) ^ update d x 0 u := by
  have : (fun u ↦ (· - u) ^ d u).mulSupport ⊆ h.toFinset := by
    simp [Function.FactorizedRational.mulSupport]
  rw [finprod_eq_prod_of_mulSupport_subset _ this, meromorphicTrailingCoeffAt_prod
      (fun _ ↦ by fun_prop), finprod_eq_prod_of_mulSupport_subset _ (mulSupport_update h)]
  apply Finset.prod_congr rfl
  intro y hy
  rw [MeromorphicAt.meromorphicTrailingCoeffAt_zpow (by fun_prop)]
  by_cases hxy : x = y
  · rw [hxy, meromorphicTrailingCoeffAt_id_sub_const]
    simp_all
  · grind [meromorphicTrailingCoeffAt_id_sub_const]

theorem meromorphicTrailingCoeffAt_factorizedRational_off_support {d : 𝕜 → ℤ} {x : 𝕜}
    (h₁ : d.HasFiniteSupport) (h₂ : x ∉ d.support) :
    meromorphicTrailingCoeffAt (∏ᶠ u, (· - u) ^ d u) x = ∏ᶠ u, (x - u) ^ d u := by
  classical
  rw [meromorphicTrailingCoeffAt_factorizedRational h₁,
    finprod_eq_prod_of_mulSupport_subset _ (mulSupport_update h₁)]
  have : (fun u ↦ (x - u) ^ d u).mulSupport ⊆ h₁.toFinset := by
    intro u
    contrapose
    simp_all
  rw [finprod_eq_prod_of_mulSupport_subset _ this, Finset.prod_congr rfl]
  intro y hy
  congr
  apply Function.update_of_ne
  by_contra hCon
  simp_all

theorem log_norm_meromorphicTrailingCoeffAt {d : 𝕜 → ℤ} {x : 𝕜} (h : d.HasFiniteSupport) :
    log ‖meromorphicTrailingCoeffAt (∏ᶠ u, (· - u) ^ d u) x‖ = ∑ᶠ u, (d u) * log ‖x - u‖ := by
  classical
  rw [meromorphicTrailingCoeffAt_factorizedRational h,
    finprod_eq_prod_of_mulSupport_subset _ (mulSupport_update h)]
  have : ∀ y ∈ h.toFinset, ‖(x - y) ^ update d x 0 y‖ ≠ 0 := by
    intro y _
    by_cases h : x = y
    · rw [h]
      simp_all
    · simp_all [zpow_ne_zero, sub_ne_zero]
  rw [norm_prod, log_prod this]
  have : (fun u ↦ (d u) * log ‖x - u‖).support ⊆ h.toFinset := by
    intro u
    contrapose
    simp_all
  rw [finsum_eq_sum_of_support_subset _ this]
  apply Finset.sum_congr rfl
  intro y hy
  rw [norm_zpow, Real.log_zpow]
  by_cases h : x = y
  · simp [h]
  · rw [Function.update_of_ne (by tauto)]

end Function.FactorizedRational

open Function.FactorizedRational

/-!
## Elimination of Zeros and Poles

This section shows that every meromorphic function with finitely many zeros and poles is equivalent,
modulo equality on codiscrete sets, to the product of a factorized rational function and an analytic
function without zeros.

We provide analogous results for functions of the form `log ‖meromorphic‖`.
-/

-- DISSOLVED: MeromorphicOn.extract_zeros_poles

-- DISSOLVED: MeromorphicOn.extract_zeros_poles_log

open Classical in

-- DISSOLVED: MeromorphicOn.meromorphicTrailingCoeffAt_extract_zeros_poles

-- DISSOLVED: MeromorphicOn.log_norm_meromorphicTrailingCoeffAt_extract_zeros_poles
