/-
Extracted from RingTheory/MvPolynomial/Tower.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Algebra towers for multivariate polynomial

This file proves some basic results about the algebra tower structure for the type
`MvPolynomial σ R`.

This structure itself is provided elsewhere as `MvPolynomial.isScalarTower`

When you update this file, you can also try to make a corresponding update in
`RingTheory.Polynomial.Tower`.
-/

variable (R A B : Type*) {σ : Type*}

namespace MvPolynomial

section Semiring

variable [CommSemiring R] [CommSemiring A] [CommSemiring B]

variable [Algebra R A] [Algebra A B] [Algebra R B]

variable [IsScalarTower R A B]

variable {R B}

theorem aeval_map_algebraMap (x : σ → B) (p : MvPolynomial σ R) :
    aeval x (map (algebraMap R A) p) = aeval x p := by
  rw [aeval_def, aeval_def, eval₂_map, IsScalarTower.algebraMap_eq R A B]

end Semiring

section CommSemiring

variable [CommSemiring R] [CommSemiring A] [CommSemiring B]

variable [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]

variable {R A}

theorem aeval_algebraMap_apply (x : σ → A) (p : MvPolynomial σ R) :
    aeval (algebraMap A B ∘ x) p = algebraMap A B (MvPolynomial.aeval x p) := by
  rw [aeval_def, aeval_def, ← coe_eval₂Hom, ← coe_eval₂Hom, map_eval₂Hom, ←
    IsScalarTower.algebraMap_eq, Function.comp_def]
