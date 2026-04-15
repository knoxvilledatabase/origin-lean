/-
Extracted from RingTheory/Derivation/Basic.lean
Genuine: 2 of 6 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# Derivations

This file defines derivation. A derivation `D` from the `R`-algebra `A` to the `A`-module `M` is an
`R`-linear map that satisfy the Leibniz rule `D (a * b) = a * D b + D a * b`.

## Main results

- `Derivation`: The type of `R`-derivations from `A` to `M`. This has an `A`-module structure.
- `Derivation.llcomp`: We may compose linear maps and derivations to obtain a derivation,
  and the composition is bilinear.

See `Mathlib/RingTheory/Derivation/Lie.lean` for
- `Derivation.instLieAlgebra`: The `R`-derivations from `A` to `A` form a Lie algebra over `R`.

and `Mathlib/RingTheory/Derivation/ToSquareZero.lean` for
- `derivationToSquareZeroEquivLift`: The `R`-derivations from `A` into a square-zero ideal `I`
  of `B` corresponds to the lifts `A →ₐ[R] B` of the map `A →ₐ[R] B ⧸ I`.

## Future project

- Generalize derivations into bimodules.

-/

open Algebra

structure Derivation (R : Type*) (A : Type*) (M : Type*)
    [CommSemiring R] [CommSemiring A] [AddCommMonoid M] [Algebra R A] [Module A M] [Module R M]
    extends A →ₗ[R] M where
  protected map_one_eq_zero' : toLinearMap 1 = 0
  protected leibniz' (a b : A) : toLinearMap (a * b) = a • toLinearMap b + b • toLinearMap a

add_decl_doc Derivation.toLinearMap

namespace Derivation

variable {R : Type*} {A : Type*} {B : Type*} {M : Type*}

variable [CommSemiring R] [CommSemiring A] [CommSemiring B] [AddCommMonoid M]

variable [Algebra R A] [Algebra R B]

variable [Module A M] [Module B M] [Module R M]

variable (D : Derivation R A M) {D1 D2 : Derivation R A M} (r : R) (a b : A)

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

def Simps.apply (D : Derivation R A M) : A → M := D

initialize_simps_projections Derivation (toFun → apply)

attribute [coe] toLinearMap

-- INSTANCE (free from Core): hasCoeToLinearMap
