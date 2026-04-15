/-
Extracted from Algebra/Polynomial/Module/FiniteDimensional.lean
Genuine: 1 of 2 | Dissolved: 1 | Infrastructure: 0
-/
import Origin.Core

/-!
# Polynomial modules in finite dimensions

This file is a place to collect results about the `R[X]`-module structure induced on an `R`-module
by an `R`-linear endomorphism, which require the concept of finite-dimensionality.

## Main results:
* `Module.AEval.isTorsion_of_finiteDimensional`: if a vector space `M` with coefficients in a field
  `K` carries a natural `K`-linear endomorphism which belongs to a finite-dimensional algebra
  over `K`, then the induced `K[X]`-module structure on `M` is pure torsion.

-/

open Polynomial

variable {R K M A : Type*} {a : A}

namespace Module.AEval

-- DISSOLVED: isTorsion_of_aeval_eq_zero

variable (K M a)

theorem isTorsion_of_finiteDimensional [Field K] [Ring A] [Algebra K A]
    [AddCommGroup M] [Module A M] [Module K M] [IsScalarTower K A M] [FiniteDimensional K A] :
    IsTorsion K[X] (AEval K M a) :=
  isTorsion_of_aeval_eq_zero (minpoly.aeval K a) (minpoly.ne_zero_of_finite K a)

end Module.AEval
