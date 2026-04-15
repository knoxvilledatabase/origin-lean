/-
Extracted from RingTheory/IntegralClosure/GoingDown.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Going down for integrally closed domains

In this file, we provide the instance that any integral extension of `R ⊆ S` satisfies going down
if `R` is integrally closed.

-/

open Polynomial

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

lemma Polynomial.coeff_mem_radical_span_coeff_of_dvd
    (p : R[X]) (q : R[X]) (hp : p.Monic) (hq : q.Monic)
    (H : q ∣ p) (i : ℕ) (hi : i ≠ q.natDegree) :
    q.coeff i ∈ (Ideal.span { p.coeff i | i < p.natDegree }).radical := by
  rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
  rintro P ⟨hPJ, hP⟩
  have : p.map (Ideal.Quotient.mk P) = X ^ p.natDegree := by
    ext i
    obtain hi | rfl | hi := lt_trichotomy i p.natDegree
    · simpa [hi.ne, Ideal.Quotient.eq_zero_iff_mem] using hPJ (Ideal.subset_span ⟨_, hi, rfl⟩)
    · simp [hp]
    · simp [coeff_eq_zero_of_natDegree_lt hi, hi.ne']
  obtain ⟨j, hj, a, ha⟩ :=
    (dvd_prime_pow (prime_X (R := R ⧸ P)) _).mp (this ▸ map_dvd (Ideal.Quotient.mk P) H)
  obtain ⟨r, hr, e⟩ := isUnit_iff.mp a⁻¹.isUnit
  rw [← Units.eq_mul_inv_iff_mul_eq, ← e] at ha
  obtain rfl : j = q.natDegree := by
    simpa [hq.natDegree_map, hr.ne_zero] using congr(($ha).natDegree).symm
  simpa [hi, Ideal.Quotient.eq_zero_iff_mem] using congr(($ha).coeff i)
