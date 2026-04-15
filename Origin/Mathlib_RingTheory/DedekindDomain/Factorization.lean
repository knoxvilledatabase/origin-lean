/-
Extracted from RingTheory/DedekindDomain/Factorization.lean
Genuine: 18 | Conflates: 0 | Dissolved: 22 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Order.Filter.Cofinite
import Mathlib.RingTheory.DedekindDomain.Ideal
import Mathlib.RingTheory.UniqueFactorizationDomain.Finite

/-!
# Factorization of ideals and fractional ideals of Dedekind domains
Every nonzero ideal `I` of a Dedekind domain `R` can be factored as a product `∏_v v^{n_v}` over the
maximal ideals of `R`, where the exponents `n_v` are natural numbers.

Similarly, every nonzero fractional ideal `I` of a Dedekind domain `R` can be factored as a product
`∏_v v^{n_v}` over the maximal ideals of `R`, where the exponents `n_v` are integers. We define
`FractionalIdeal.count K v I` (abbreviated as `val_v(I)` in the documentation) to be `n_v`, and we
prove some of its properties. If `I = 0`, we define `val_v(I) = 0`.

## Main definitions
- `FractionalIdeal.count` : If `I` is a nonzero fractional ideal, `a ∈ R`, and `J` is an ideal of
  `R` such that `I = a⁻¹J`, then we define `val_v(I)` as `(val_v(J) - val_v(a))`. If `I = 0`, we
  set `val_v(I) = 0`.

## Main results
- `Ideal.finite_factors` : Only finitely many maximal ideals of `R` divide a given nonzero ideal.
- `Ideal.finprod_heightOneSpectrum_factorization` : The ideal `I` equals the finprod
  `∏_v v^(val_v(I))`, where `val_v(I)` denotes the multiplicity of `v` in the factorization of `I`
  and `v` runs over the maximal ideals of `R`.
- `FractionalIdeal.finprod_heightOneSpectrum_factorization` : If `I` is a nonzero fractional ideal,
  `a ∈ R`, and `J` is an ideal of `R` such that `I = a⁻¹J`, then `I` is equal to the product
  `∏_v v^(val_v(J) - val_v(a))`.
  - `FractionalIdeal.finprod_heightOneSpectrum_factorization'` : If `I` is a nonzero fractional
  ideal, then `I` is equal to the product `∏_v v^(val_v(I))`.
- `FractionalIdeal.finprod_heightOneSpectrum_factorization_principal` : For a nonzero `k = r/s ∈ K`,
  the fractional ideal `(k)` is equal to the product `∏_v v^(val_v(r) - val_v(s))`.
- `FractionalIdeal.finite_factors` : If `I ≠ 0`, then `val_v(I) = 0` for all but finitely many
  maximal ideals of `R`.

## Implementation notes
Since we are only interested in the factorization of nonzero fractional ideals, we define
`val_v(0) = 0` so that every `val_v` is in `ℤ` and we can avoid having to use `WithTop ℤ`.

## Tags
dedekind domain, fractional ideal, ideal, factorization
-/

noncomputable section

open scoped Classical nonZeroDivisors

open Set Function UniqueFactorizationMonoid IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

  Classical

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-! ### Factorization of ideals of Dedekind domains -/

variable [IsDedekindDomain R] (v : HeightOneSpectrum R)

def IsDedekindDomain.HeightOneSpectrum.maxPowDividing (I : Ideal R) : Ideal R :=
  v.asIdeal ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors

-- DISSOLVED: Ideal.finite_factors

-- DISSOLVED: Associates.finite_factors

namespace Ideal

-- DISSOLVED: finite_mulSupport

-- DISSOLVED: finite_mulSupport_coe

-- DISSOLVED: finite_mulSupport_inv

-- DISSOLVED: finprod_not_dvd

end Ideal

-- DISSOLVED: Associates.finprod_ne_zero

namespace Ideal

-- DISSOLVED: finprod_count

-- DISSOLVED: finprod_heightOneSpectrum_factorization

variable (K)

-- DISSOLVED: finprod_heightOneSpectrum_factorization_coe

end Ideal

/-! ### Factorization of fractional ideals of Dedekind domains -/

namespace FractionalIdeal

open Int IsLocalization

-- DISSOLVED: finprod_heightOneSpectrum_factorization

-- DISSOLVED: finprod_heightOneSpectrum_factorization_principal_fraction

-- DISSOLVED: finprod_heightOneSpectrum_factorization_principal

variable (K)

def count (I : FractionalIdeal R⁰ K) : ℤ :=
  dite (I = 0) (fun _ : I = 0 => 0) fun _ : ¬I = 0 =>
    let a := choose (exists_eq_spanSingleton_mul I)
    let J := choose (choose_spec (exists_eq_spanSingleton_mul I))
    ((Associates.mk v.asIdeal).count (Associates.mk J).factors -
        (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {a})).factors : ℤ)

lemma count_zero : count K v (0 : FractionalIdeal R⁰ K) = 0 := by simp only [count, dif_pos]

-- DISSOLVED: count_ne_zero

-- DISSOLVED: count_well_defined

-- DISSOLVED: count_mul

-- DISSOLVED: count_mul'

theorem count_one : count K v (1 : FractionalIdeal R⁰ K) = 0 := by
  have h1 : (1 : FractionalIdeal R⁰ K) =
      spanSingleton R⁰ ((algebraMap R K) 1)⁻¹ * ↑(1 : Ideal R) := by
    rw [(algebraMap R K).map_one, Ideal.one_eq_top, coeIdeal_top, mul_one, inv_one,
      spanSingleton_one]
  rw [count_well_defined K v one_ne_zero h1, Ideal.span_singleton_one, Ideal.one_eq_top, sub_self]

-- DISSOLVED: count_prod

theorem count_pow (n : ℕ) (I : FractionalIdeal R⁰ K) :
    count K v (I ^ n) = n * count K v I := by
  induction' n with n h
  · rw [pow_zero, ofNat_zero, MulZeroClass.zero_mul, count_one]
  · rw [pow_succ, count_mul']
    by_cases hI : I = 0
    · have h_neg : ¬(I ^ n ≠ 0 ∧ I ≠ 0) := by
        rw [not_and', not_not, ne_eq]
        intro h
        exact absurd hI h
      rw [if_neg h_neg, hI, count_zero, MulZeroClass.mul_zero]
    · rw [if_pos (And.intro (pow_ne_zero n hI) hI), h, Nat.cast_add,
        Nat.cast_one]
      ring

theorem count_self : count K v (v.asIdeal : FractionalIdeal R⁰ K) = 1 := by
  have hv : (v.asIdeal : FractionalIdeal R⁰ K) ≠ 0 := coeIdeal_ne_zero.mpr v.ne_bot
  have h_self : (v.asIdeal : FractionalIdeal R⁰ K) =
      spanSingleton R⁰ ((algebraMap R K) 1)⁻¹ * ↑v.asIdeal := by
    rw [(algebraMap R K).map_one, inv_one, spanSingleton_one, one_mul]
  have hv_irred : Irreducible (Associates.mk v.asIdeal) := by apply v.associates_irreducible
  rw [count_well_defined K v hv h_self, Associates.count_self hv_irred, Ideal.span_singleton_one,
    ← Ideal.one_eq_top, Associates.mk_one, Associates.factors_one, Associates.count_zero hv_irred,
    ofNat_zero, sub_zero, ofNat_one]

theorem count_pow_self (n : ℕ) :
    count K v ((v.asIdeal : FractionalIdeal R⁰ K) ^ n) = n := by
  rw [count_pow, count_self, mul_one]

theorem count_neg_zpow (n : ℤ) (I : FractionalIdeal R⁰ K) :
    count K v (I ^ (-n)) = - count K v (I ^ n) := by
  by_cases hI : I = 0
  · by_cases hn : n = 0
    · rw [hn, neg_zero, zpow_zero, count_one, neg_zero]
    · rw [hI, zero_zpow n hn, zero_zpow (-n) (neg_ne_zero.mpr hn), count_zero, neg_zero]
  · rw [eq_neg_iff_add_eq_zero, ← count_mul K v (zpow_ne_zero _ hI) (zpow_ne_zero _ hI),
      ← zpow_add₀ hI, neg_add_cancel, zpow_zero]
    exact count_one K v

theorem count_inv (I : FractionalIdeal R⁰ K) :
    count K v (I⁻¹) = - count K v I := by
  rw [← zpow_neg_one, count_neg_zpow K v (1 : ℤ) I, zpow_one]

theorem count_zpow (n : ℤ) (I : FractionalIdeal R⁰ K) :
    count K v (I ^ n) = n * count K v I := by
  cases' n with n
  · rw [ofNat_eq_coe, zpow_natCast]
    exact count_pow K v n I
  · rw [negSucc_coe, count_neg_zpow, zpow_natCast, count_pow]
    ring

theorem count_zpow_self (n : ℤ) :
    count K v ((v.asIdeal : FractionalIdeal R⁰ K) ^ n) = n := by
  rw [count_zpow, count_self, mul_one]

theorem count_maximal_coprime {w : HeightOneSpectrum R} (hw : w ≠ v) :
    count K v (w.asIdeal : FractionalIdeal R⁰ K) = 0 := by
  have hw_fact : (w.asIdeal : FractionalIdeal R⁰ K) =
      spanSingleton R⁰ ((algebraMap R K) 1)⁻¹ * ↑w.asIdeal := by
    rw [(algebraMap R K).map_one, inv_one, spanSingleton_one, one_mul]
  have hw_ne_zero : (w.asIdeal : FractionalIdeal R⁰ K) ≠ 0 :=
    coeIdeal_ne_zero.mpr w.ne_bot
  have hv : Irreducible (Associates.mk v.asIdeal) := by apply v.associates_irreducible
  have hw' : Irreducible (Associates.mk w.asIdeal) := by apply w.associates_irreducible
  rw [count_well_defined K v hw_ne_zero hw_fact, Ideal.span_singleton_one, ← Ideal.one_eq_top,
    Associates.mk_one, Associates.factors_one, Associates.count_zero hv, ofNat_zero, sub_zero,
    natCast_eq_zero, ← pow_one (Associates.mk w.asIdeal), Associates.factors_prime_pow hw',
    Associates.count_some hv, Multiset.replicate_one, Multiset.count_eq_zero,
    Multiset.mem_singleton]
  simp only [Subtype.mk.injEq]
  rw [Associates.mk_eq_mk_iff_associated, associated_iff_eq, ← HeightOneSpectrum.ext_iff]
  exact Ne.symm hw

theorem count_maximal (w : HeightOneSpectrum R) :
    count K v (w.asIdeal : FractionalIdeal R⁰ K) = if w = v then 1 else 0 := by
  split_ifs with h
  · rw [h, count_self]
  · exact count_maximal_coprime K v h

theorem count_finprod_coprime (exps : HeightOneSpectrum R → ℤ) :
    count K v (∏ᶠ (w : HeightOneSpectrum R) (_ : w ≠ v),
      (w.asIdeal : (FractionalIdeal R⁰ K)) ^ exps w) = 0 := by
  apply finprod_mem_induction fun I => count K v I = 0
  · exact count_one K v
  · intro I I' hI hI'
    by_cases h : I ≠ 0 ∧ I' ≠ 0
    · rw [count_mul' K v, if_pos h, hI, hI', add_zero]
    · rw [count_mul' K v, if_neg h]
  · intro w hw
    rw [count_zpow, count_maximal_coprime K v hw, MulZeroClass.mul_zero]

theorem count_finsupp_prod (exps : HeightOneSpectrum R →₀ ℤ) :
    count K v (exps.prod (HeightOneSpectrum.asIdeal · ^ ·)) = exps v := by
  rw [Finsupp.prod, count_prod]
  · simp only [count_zpow, count_maximal, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      exps.mem_support_iff, ne_eq, ite_not, ite_eq_right_iff, @eq_comm ℤ 0, imp_self]
  · exact fun v hv ↦ zpow_ne_zero _ (coeIdeal_ne_zero.mpr v.ne_bot)

theorem count_finprod (exps : HeightOneSpectrum R → ℤ)
    (h_exps : ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite, exps v = 0) :
    count K v (∏ᶠ v : HeightOneSpectrum R,
      (v.asIdeal : FractionalIdeal R⁰ K) ^ exps v) = exps v := by
  convert count_finsupp_prod K v (Finsupp.mk h_exps.toFinset exps (fun _ ↦ h_exps.mem_toFinset))
  rw [finprod_eq_finset_prod_of_mulSupport_subset (s := h_exps.toFinset), Finsupp.prod]
  · rfl
  · rw [Finite.coe_toFinset]
    intro v hv h
    rw [mem_mulSupport, h, zpow_zero] at hv
    exact hv (Eq.refl 1)

-- DISSOLVED: count_coe

theorem count_coe_nonneg (J : Ideal R) : 0 ≤ count K v J := by
  by_cases hJ : J = 0
  · simp only [hJ, Submodule.zero_eq_bot, coeIdeal_bot, count_zero, le_refl]
  · simp only [count_coe K v hJ, Nat.cast_nonneg]

-- DISSOLVED: count_mono

-- DISSOLVED: finprod_heightOneSpectrum_factorization'

variable {K}

-- DISSOLVED: finite_factors'

theorem finite_factors (I : FractionalIdeal R⁰ K) :
    ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite, count K v I = 0 := by
  by_cases hI : I = 0
  · simp only [hI, count_zero, Filter.eventually_cofinite, not_true_eq_false, setOf_false,
      finite_empty]
  · convert finite_factors' hI (choose_spec (choose_spec (exists_eq_spanSingleton_mul I))).2
    rw [count_ne_zero K _ hI]

end FractionalIdeal
