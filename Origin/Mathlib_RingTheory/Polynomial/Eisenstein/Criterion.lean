/-
Extracted from RingTheory/Polynomial/Eisenstein/Criterion.lean
Genuine: 1 of 3 | Dissolved: 2 | Infrastructure: 0
-/
import Origin.Core

/-! # The Eisenstein criterion

- `Polynomial.generalizedEisenstein` :
  Let `R` be an integral domain
  and let `K` an `R`-algebra which is a field
  Let `q : R[X]` be a monic polynomial which is prime in `K[X]`.
  Let `f : R[X]` be a polynomial of strictly positive degree
  satisfying the following properties:
  * the image of `f` in `K[X]` is a power of `q`.
  * the leading coefficient of `f` is not zero in `K`
  * the polynomial `f` is primitive.

  Assume moreover that `f.modByMonic q` is not zero in `(R ⧸ (P ^ 2))[X]`,
  where `P` is the kernel of `algebraMap R K`.
  Then `f` is irreducible.

We give in `Archive.Examples.Eisenstein` an explicit example
of application of this criterion.

* `Polynomial.irreducible_of_eisenstein_criterion` : the classic Eisenstein criterion.
  It is the particular case where `q := X`.

## TODO

The case of a polynomial `q := X - a` is interesting,
then the mod `P ^ 2` hypothesis can rephrased as saying
that `f.derivative.eval a ∉ P ^ 2`. (TODO)
The case of cyclotomic polynomials of prime index `p`
could be proved directly using that result, taking `a = 1`.

The result can also be generalized to the case where
the leading coefficients of `f` and `q` do not belong to `P`.
(By localization at `P`, make these coefficients invertible.)
There are two obstructions, though :

* Usually, one will only obtain irreducibility in `F[X]`, where `F` is the field
  of fractions of `R`. (If `R` is a UFD, this will be close to what is wanted,
  but not in general.)

* The mod `P ^ 2` hypothesis will have to be rephrased to a condition
  in the second symbolic power of `P`. When `P` is a maximal ideal,
  that symbolic power coincides with `P ^ 2`, but not in general.

-/

namespace Polynomial

open Ideal.Quotient Ideal RingHom

variable {R : Type*} [CommRing R] [IsDomain R]
  {K : Type*} [Field K] [Algebra R K]

-- DISSOLVED: generalizedEisenstein_aux

-- DISSOLVED: generalizedEisenstein

theorem irreducible_of_eisenstein_criterion {f : R[X]} {P : Ideal R} (hP : P.IsPrime)
    (hfl : f.leadingCoeff ∉ P)
    (hfP : ∀ n : ℕ, ↑n < degree f → f.coeff n ∈ P) (hfd0 : 0 < degree f)
    (h0 : f.coeff 0 ∉ P ^ 2) (hu : f.IsPrimitive) : Irreducible f := by
  apply generalizedEisenstein (K := FractionRing (R ⧸ P)) (q := X) (p := f.natDegree)
    (by simp [map_X, irreducible_X]) monic_X hu
    (natDegree_pos_iff_degree_pos.mpr hfd0)
  · simp only [IsScalarTower.algebraMap_eq R (R ⧸ P) (FractionRing (R ⧸ P)),
      Quotient.algebraMap_eq, coe_comp, Function.comp_apply, ne_eq,
      FaithfulSMul.algebraMap_eq_zero_iff]
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact hfl
  · rw [← map_C, ← Polynomial.map_pow, ← Polynomial.map_mul]
    simp only [IsScalarTower.algebraMap_eq R (R ⧸ P) (FractionRing (R ⧸ P)),
      Quotient.algebraMap_eq, ← map_map]
    congr 1
    ext n
    simp only [coeff_map, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero, sub_ite, sub_zero]
    split_ifs with hn
    · rw [hn, leadingCoeff, sub_self]
      exact zero_mem _
    · by_cases hn' : n < f.natDegree
      · exact hfP _ (coe_lt_degree.mpr hn')
      · rw [f.coeff_eq_zero_of_natDegree_lt]
        · exact P.zero_mem
        · simp [Nat.lt_iff_le_and_ne, ← Nat.not_lt, hn', Ne.symm hn]
  · rw [modByMonic_X, map_C, ne_eq, C_eq_zero, Ideal.Quotient.eq_zero_iff_mem,
      ← coeff_zero_eq_eval_zero]
    convert h0
    · rw [IsScalarTower.algebraMap_eq R (R ⧸ P) (FractionRing (R ⧸ P))]
      rw [ker_comp_of_injective]
      · ext a; simp
      · exact FaithfulSMul.algebraMap_injective (R ⧸ P) (FractionRing (R ⧸ P))

end Polynomial
