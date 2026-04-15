/-
Extracted from RingTheory/Polynomial/UniversalFactorizationRing.lean
Genuine: 6 of 6 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Universal factorization ring

Let `R` be a commutative ring and `p : R[X]` be monic of degree `n` and let `n = m + k`.
We construct the universal ring of the following functors on `R-Alg`:
- `S ↦ "monic polynomials over S of degree n"`:
  Represented by `R[X₁,...,Xₙ]`. See `MvPolynomial.mapEquivMonic`.
- `S ↦ "factorizations of p into (monic deg m) * (monic deg k) in S"`:
  Represented by an `R`-algebra (`Polynomial.UniversalFactorizationRing`) that is finitely-presented
  as an `R`-module. See `Polynomial.UniversalFactorizationRing.homEquiv`.
- `S ↦ "factorizations of p into coprime (monic deg m) * (monic deg k) in S"`:
  Represented by an etale `R`-algebra (`Polynomial.UniversalCoprimeFactorizationRing`).
  See `Polynomial.UniversalCoprimeFactorizationRing.homEquiv`.

-/

open scoped Polynomial TensorProduct

open RingHomClass (toRingHom)

variable (R S T : Type*) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]

variable (n m k : ℕ) (hn : n = m + k)

noncomputable section

namespace Polynomial

def freeMonic : (MvPolynomial (Fin n) R)[X] :=
  .X ^ n + ∑ i : Fin n, .C (.X i) * .X ^ (i : ℕ)

lemma coeff_freeMonic :
    (freeMonic R n).coeff k = if h : k < n then .X ⟨k, h⟩ else if k = n then 1 else 0 := by
  simp only [freeMonic, Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.finset_sum_coeff,
    Polynomial.coeff_C_mul, mul_ite, mul_one, mul_zero]
  by_cases h : k < n
  · simp +contextual [Finset.sum_eq_single (ι := Fin n) (a := ⟨k, h⟩),
      Fin.ext_iff, @eq_comm _ k, h, h.ne']
  · rw [Finset.sum_eq_zero fun x _ ↦ if_neg (by cases x; lia), add_zero, dif_neg h]

lemma degree_freeMonic [Nontrivial R] : (freeMonic R n).degree = n :=
  Polynomial.degree_eq_of_le_of_coeff_ne_zero ((Polynomial.degree_le_iff_coeff_zero _ _).mpr
    (by simp +contextual [coeff_freeMonic, LT.lt.not_gt, LT.lt.ne']))
    (by simp [coeff_freeMonic])

lemma natDegree_freeMonic [Nontrivial R] : (freeMonic R n).natDegree = n :=
  natDegree_eq_of_degree_eq_some (degree_freeMonic R n)

lemma monic_freeMonic : (freeMonic R n).Monic := by
  nontriviality R
  simp [Polynomial.Monic, ← Polynomial.coeff_natDegree, natDegree_freeMonic, coeff_freeMonic]

omit [Algebra R S] in

lemma map_map_freeMonic (f : R →+* S) :
    (freeMonic R n).map (MvPolynomial.map f) = freeMonic S n := by
  simp [freeMonic, Polynomial.map_sum]

open Polynomial (MonicDegreeEq)
