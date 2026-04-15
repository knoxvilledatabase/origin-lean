/-
Extracted from FieldTheory/Finite/Polynomial.lean
Genuine: 8 of 8 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
## Polynomials over finite fields
-/

namespace MvPolynomial

variable {σ : Type*}

theorem C_dvd_iff_zmod (n : ℕ) (φ : MvPolynomial σ ℤ) :
    C (n : ℤ) ∣ φ ↔ map (Int.castRingHom (ZMod n)) φ = 0 :=
  C_dvd_iff_map_hom_eq_zero _ _ (CharP.intCast_eq_zero_iff (ZMod n) n) _

section frobenius

variable {p : ℕ} [Fact p.Prime]

theorem frobenius_zmod (f : MvPolynomial σ (ZMod p)) : frobenius _ p f = expand p f := by
  apply induction_on f
  · intro a; rw [expand_C, frobenius_def, ← C_pow, ZMod.pow_card]
  · simp only [map_add]; intro _ _ hf hg; rw [hf, hg]
  · simp only [expand_X, map_mul]
    intro _ _ hf; rw [hf, frobenius_def]

theorem expand_zmod (f : MvPolynomial σ (ZMod p)) : expand p f = f ^ p :=
  (frobenius_zmod _).symm

end frobenius

end MvPolynomial

namespace MvPolynomial

noncomputable section

open Set LinearMap Submodule

variable {K : Type*} {σ : Type*}

section Indicator

variable [Fintype K] [Fintype σ]

def indicator [CommRing K] (a : σ → K) : MvPolynomial σ K :=
  ∏ n, (1 - (X n - C (a n)) ^ (Fintype.card K - 1))

section CommRing

variable [CommRing K]

theorem eval_indicator_apply_eq_one (a : σ → K) : eval a (indicator a) = 1 := by
  nontriviality
  have : 0 < Fintype.card K - 1 := tsub_pos_of_lt Fintype.one_lt_card
  simp only [indicator, map_prod, map_sub, map_one, map_pow, eval_X, eval_C, sub_self,
    zero_pow this.ne', sub_zero, Finset.prod_const_one]

theorem degrees_indicator (c : σ → K) :
    degrees (indicator c) ≤ ∑ s : σ, (Fintype.card K - 1) • {s} := by
  rw [indicator]
  classical
  refine degrees_prod_le.trans <| Finset.sum_le_sum fun s _ ↦ degrees_sub_le.trans ?_
  rw [degrees_one, Multiset.zero_union]
  refine le_trans degrees_pow_le (nsmul_le_nsmul_right ?_ _)
  refine degrees_sub_le.trans ?_
  rw [degrees_C, Multiset.union_zero]
  exact degrees_X' _

theorem indicator_mem_restrictDegree (c : σ → K) :
    indicator c ∈ restrictDegree σ K (Fintype.card K - 1) := by
  classical
  rw [mem_restrictDegree_iff_sup, indicator]
  intro n
  refine le_trans (Multiset.count_le_of_le _ <| degrees_indicator _) (le_of_eq ?_)
  simp_rw [← Multiset.coe_countAddMonoidHom, map_sum,
    map_nsmul, Multiset.coe_countAddMonoidHom, nsmul_eq_mul, Nat.cast_id]
  trans
  · refine Finset.sum_eq_single n ?_ ?_
    · intro b _ ne
      simp [Multiset.count_singleton, ne, if_neg (Ne.symm _)]
    · intro h; exact (h <| Finset.mem_univ _).elim
  · rw [Multiset.count_singleton_self, mul_one]

end CommRing

variable [Field K]

theorem eval_indicator_apply_eq_zero (a b : σ → K) (h : a ≠ b) : eval a (indicator b) = 0 := by
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ b i := by rwa [Ne, funext_iff, not_forall] at h
  simp only [indicator, map_prod, map_sub, map_one, map_pow, eval_X, eval_C,
    Finset.prod_eq_zero_iff]
  refine ⟨i, Finset.mem_univ _, ?_⟩
  rw [FiniteField.pow_card_sub_one_eq_one, sub_self]
  rwa [Ne, sub_eq_zero]

end Indicator

variable (K σ)
