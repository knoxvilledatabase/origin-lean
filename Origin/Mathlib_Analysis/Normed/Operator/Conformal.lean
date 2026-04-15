/-
Extracted from Analysis/Normed/Operator/Conformal.lean
Genuine: 3 of 5 | Dissolved: 2 | Infrastructure: 0
-/
import Origin.Core

/-!
# Conformal Linear Maps

A continuous linear map between `R`-normed spaces `X` and `Y` `IsConformalMap` if it is
a nonzero multiple of a linear isometry.

## Main definitions

* `IsConformalMap`: the main definition of conformal linear maps

## Main results

* The conformality of the composition of two conformal linear maps, the identity map
  and multiplications by nonzero constants as continuous linear maps
* `isConformalMap_of_subsingleton`: all continuous linear maps on singleton spaces are conformal

See `Analysis.InnerProductSpace.ConformalLinearMap` for
* `isConformalMap_iff`: a map between inner product spaces is conformal
  iff it preserves inner products up to a fixed scalar factor.


## Tags

conformal

## Warning

The definition of conformality in this file does NOT require the maps to be orientation-preserving.
-/

noncomputable section

open Function LinearIsometry ContinuousLinearMap

def IsConformalMap {R : Type*} {X Y : Type*} [NormedField R] [SeminormedAddCommGroup X]
    [SeminormedAddCommGroup Y] [NormedSpace R X] [NormedSpace R Y] (f' : X →L[R] Y) :=
  ∃ c ≠ (0 : R), ∃ li : X →ₗᵢ[R] Y, f' = c • li.toContinuousLinearMap

variable {R M N G M' : Type*} [NormedField R] [SeminormedAddCommGroup M] [SeminormedAddCommGroup N]
  [SeminormedAddCommGroup G] [NormedSpace R M] [NormedSpace R N] [NormedSpace R G]
  [NormedAddCommGroup M'] [NormedSpace R M'] {f : M →L[R] N} {g : N →L[R] G} {c : R}

theorem isConformalMap_id : IsConformalMap (.id R M) :=
  ⟨1, one_ne_zero, id, by simp⟩

-- DISSOLVED: IsConformalMap.smul

-- DISSOLVED: isConformalMap_const_smul

protected theorem LinearIsometry.isConformalMap (f' : M →ₗᵢ[R] N) :
    IsConformalMap f'.toContinuousLinearMap :=
  ⟨1, one_ne_zero, f', (one_smul _ _).symm⟩
