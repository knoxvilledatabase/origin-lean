/-
Extracted from Analysis/Normed/Field/Approximation.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Approximate roots and polynomials in a normed field

In this file, we prove several approximation lemmas on a normed field.

## Main results
- `Polynomial.exists_roots_norm_sub_lt_of_norm_coeff_sub_lt` :  **Continuity of Roots.**
Let `f` and `g` be two monic polynomials such that `g` splits. If the coefficients of two
polynomials `f` and `g` are sufficiently close, then every root of `f` has a corresponding root
of `g` nearby.

- `Polynomial.exists_monic_and_natDegree_eq_and_norm_map_algebraMap_coeff_sub_lt` : Let `K` be a
dense subfield of a normed field `L`. Every monic polynomial in `L` can be approximated by
a monic polynomial in `K` of the same degree.

## TODO
Use the fact that `f.discr` is polynomial of the coefficients of `f` to show that
every polynomial `f` can be approximated by a *separable* polynomial. This result can be used
to show that the completion a separably closed field is algebraically closed, upgrading the
current theorem `IsAlgClosed.of_denseRange`.

## Tags
Approximation, polynomial, normed field, continuity of roots
-/

variable {K L : Type*}

namespace Polynomial

section ContinuityOfRoots

variable [NormedField K] [NormedField L] [NormedAlgebra K L] {f g : Polynomial K}
  {f g : Polynomial K} {ε : ℝ}

theorem exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt (hε : 0 < ε) {a : L} (ha : f.aeval a = 0)
    (hfm : f.Monic) (hgm : g.Monic) (hdeg : g.natDegree = f.natDegree)
    (hcoeff : ∀ i : ℕ, ‖g.coeff i - f.coeff i‖ < ε) (hg : (g.map (algebraMap K L)).Splits) :
    ∃ b ∈ g.aroots L, ‖a - b‖ < ((f.natDegree + 1) * ε) ^ (f.natDegree : ℝ)⁻¹ * max ‖a‖ 1 := by
  obtain ⟨b, h1, h2⟩ := exists_roots_norm_sub_lt_of_norm_coeff_sub_lt hε
      (f := f.map (algebraMap K L)) (by simpa using ha) (hfm.map _) (hgm.map _)
      (by simpa using hdeg) (by simpa [← map_sub] using hcoeff) hg
  use b, h1
  simpa using h2

end ContinuityOfRoots

section Approximation

variable [Field K] [NormedField L] [Algebra K L]

theorem exists_monic_and_natDegree_eq_and_norm_map_algebraMap_coeff_sub_lt
    (hd : DenseRange (algebraMap K L)) {f : Polynomial L} (hf : f.Monic) {ε : ℝ} (hε : ε > 0) :
    ∃ g : Polynomial K, g.Monic ∧ f.natDegree = g.natDegree ∧ ∀ n : ℕ,
    ‖(g.map (algebraMap K L)).coeff n - f.coeff n‖ < ε := by
  by_cases h : f.natDegree = 0
  · use 1
    rw [hf.natDegree_eq_zero.mp]
    · simp only [monic_one, natDegree_one, Polynomial.map_one, sub_self, norm_zero, hε,
      implies_true, and_self]
    · exact h
  choose c hc using fun i ↦ Metric.denseRange_iff.mp hd (f.coeff i) ε hε
  have hdeg : (C 1 * X ^ f.natDegree + ∑ i < f.natDegree, C (c i) * X ^ i).natDegree
      = f.natDegree := by
    calc
      _ = (C (1 : K) * X ^ f.natDegree).natDegree := by
        apply Polynomial.natDegree_add_eq_left_of_natDegree_lt
        simp only [map_one, one_mul, natDegree_pow, natDegree_X, mul_one]
        rw [← Nat.le_sub_one_iff_lt (Nat.pos_of_ne_zero h)]
        apply Polynomial.natDegree_sum_le_of_forall_le
        refine fun i hi ↦ (Polynomial.natDegree_C_mul_X_pow_le _ _).trans ?_
        simpa [Nat.le_sub_one_iff_lt (Nat.pos_of_ne_zero h)] using hi
      _ = f.natDegree := by
        simp
  use C 1 * X ^ f.natDegree + ∑ i < f.natDegree, C (c i) * X ^ i
  refine ⟨?_, hdeg.symm, fun n ↦ ?_⟩
  · rw [Monic, leadingCoeff, hdeg]
    simp
  · rcases lt_trichotomy n f.natDegree with h | h | h
    · simpa [h, ne_of_lt h, ← dist_eq_norm_sub'] using hc n
    · simp [h, hf, hε]
    · simp [not_lt_of_gt h, ne_of_gt h, coeff_eq_zero_of_natDegree_lt h, hε]

end Approximation

end Polynomial
