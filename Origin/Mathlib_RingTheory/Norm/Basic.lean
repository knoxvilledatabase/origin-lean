/-
Extracted from RingTheory/Norm/Basic.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Norm for (finite) ring extensions

Suppose we have an `R`-algebra `S` with a finite basis. For each `s : S`,
the determinant of the linear map given by multiplying by `s` gives information
about the roots of the minimal polynomial of `s` over `R`.

## Implementation notes

Typically, the norm is defined specifically for finite field extensions.
The current definition is as general as possible and the assumption that we have
fields or that the extension is finite is added to the lemmas as needed.

We only define the norm for left multiplication (`Algebra.leftMulMatrix`,
i.e. `LinearMap.mulLeft`).
For now, the definitions assume `S` is commutative, so the choice doesn't
matter anyway.

See also `Algebra.trace`, which is defined similarly as the trace of
`Algebra.leftMulMatrix`.

## References

* https://en.wikipedia.org/wiki/Field_norm

-/

universe u v w

variable {R S T : Type*} [CommRing R] [Ring S]

variable [Algebra R S]

variable {K L F : Type*} [Field K] [Field L] [Field F]

variable [Algebra K L] [Algebra K F]

variable {ι : Type w}

open Module

open LinearMap

open Matrix Polynomial

open scoped Matrix

namespace Algebra

section EqProdRoots

theorem PowerBasis.norm_gen_eq_coeff_zero_minpoly (pb : PowerBasis R S) :
    norm R pb.gen = (-1) ^ pb.dim * coeff (minpoly R pb.gen) 0 := by
  rw [norm_eq_matrix_det pb.basis, det_eq_sign_charpoly_coeff, charpoly_leftMulMatrix,
    Fintype.card_fin]

theorem PowerBasis.norm_gen_eq_prod_roots [Algebra R F] (pb : PowerBasis R S)
    (hf : ((minpoly R pb.gen).map (algebraMap R F)).Splits) :
    algebraMap R F (norm R pb.gen) = ((minpoly R pb.gen).aroots F).prod := by
  haveI := Module.nontrivial R F
  have := minpoly.monic pb.isIntegral_gen
  rw [PowerBasis.norm_gen_eq_coeff_zero_minpoly, ← pb.natDegree_minpoly, map_mul,
    ← coeff_map,
    hf.coeff_zero_eq_prod_roots_of_monic (this.map _),
    this.natDegree_map, map_pow, ← mul_assoc, ← mul_pow]
  simp only [map_neg, map_one, neg_mul, neg_neg, one_pow, one_mul]

end EqProdRoots

section EqZeroIff

variable [Finite ι]
