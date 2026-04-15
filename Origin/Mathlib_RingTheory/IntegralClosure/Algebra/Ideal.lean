/-
Extracted from RingTheory/IntegralClosure/Algebra/Ideal.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!

# Integrality over ideals

## Main results
- `Polynomial.exists_monic_aeval_eq_zero_forall_mem_of_mem_map`:
  If `S` is an integral `R`-algebra, and `I` is an ideal of `R`,
  then any `x ∈ IS` is integral over `I`, i.e. it is a root
  of some monic polynomial in `R[X]` whose non-leading coefficients are in `I`.

## Note
We actually prove something stronger, namely that the `Xⁿ⁻ⁱ`-th coefficient lives in `Iⁿ`.
This is the definition that `x` is integral over `I` in https://stacks.math.columbia.edu/tag/00H2.

-/

namespace Polynomial

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

lemma coeff_mem_pow_of_mem_adjoin_C_mul_X {R : Type*} [CommRing R]
    {I : Ideal R} {P : R[X]} (hP : P ∈ Algebra.adjoin R { C r * X | r ∈ I }) (i : ℕ) :
    P.coeff i ∈ I ^ i := by
  induction hP using Algebra.adjoin_induction generalizing i with
  | mem x hx =>
    obtain ⟨r, hrI, rfl⟩ := hx
    simp +contextual [coeff_X, apply_ite, hrI, @eq_comm _ 1]
  | algebraMap r => simp +contextual [coeff_C, apply_ite]
  | add x y hx hy _ _ => aesop
  | mul x y _ _ hx hy =>
    rw [coeff_mul]
    refine sum_mem fun ⟨j₁, j₂⟩ hj ↦ ?_
    obtain rfl : j₁ + j₂ = i := by simpa using hj
    exact pow_add I j₁ j₂ ▸ Ideal.mul_mem_mul (hx _) (hy _)

attribute [local instance] Polynomial.algebra in

lemma exists_monic_aeval_eq_zero_forall_mem_pow_of_isIntegral
    {I : Ideal R} {x : S}
    (hx : IsIntegral (Algebra.adjoin R { C r * X | r ∈ I }) (C x * X)) :
    ∃ p : R[X], p.Monic ∧ aeval x p = 0 ∧ ∀ i, p.coeff i ∈ I ^ (p.natDegree - i) := by
  cases subsingleton_or_nontrivial R
  · use 0; simp [Monic, Subsingleton.elim (α := R) 0 1]
  obtain ⟨p, hp, e⟩ := hx
  let q : R[X] := ∑ i ∈ Finset.range (p.natDegree + 1),
    C ((p.coeff i).1.coeff (p.natDegree - i)) * X ^ i
  have hq : q.natDegree = p.natDegree := by
    refine natDegree_eq_of_le_of_coeff_ne_zero (natDegree_sum_le_of_forall_le _ _ ?_) ?_
    · exact fun i hi ↦ (natDegree_C_mul_X_pow_le _ _).trans (by simpa [Nat.lt_succ_iff] using hi)
    · simp [q, hp]
  refine ⟨q, ?_, ?_, ?_⟩
  · simpa [← hq] using show q.coeff p.natDegree = 1 by simp [q, hp]
  · replace e := congr(($e).coeff p.natDegree)
    simp only [eval₂_eq_sum_range, finset_sum_coeff, coeff_zero] at e
    simp only [q, map_sum, map_mul, aeval_C, map_pow, aeval_X]
    refine (Finset.sum_congr rfl fun i hi ↦ ?_).trans e
    simp only [Finset.mem_range, Nat.lt_succ_iff] at hi
    rw [mul_pow, mul_left_comm, ← map_pow, coeff_C_mul, coeff_mul_X_pow', if_pos hi, mul_comm]
    simp [Subalgebra.algebraMap_def]
  · rw [hq]
    simp [q, apply_ite, coeff_mem_pow_of_mem_adjoin_C_mul_X (p.coeff _).2]
