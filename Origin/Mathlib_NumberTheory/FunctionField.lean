/-
Extracted from NumberTheory/FunctionField.lean
Genuine: 6 of 12 | Dissolved: 0 | Infrastructure: 6
-/
import Origin.Core

/-!
# Function fields

This file defines a function field and the ring of integers corresponding to it.

## Main definitions

- `FunctionField F K` states that `K` is a function field over the field `F`,
  i.e. it is a finite extension of the field of rational functions in one variable over `F`.
- `FunctionField.ringOfIntegers` defines the ring of integers corresponding to a function field
  as the integral closure of `F[X]` in the function field.

## Implementation notes
The definitions that involve a field of fractions choose a canonical field of fractions,
but are independent of that choice. We also omit assumptions like
`IsScalarTower F[X] (FractionRing F[X]) K` in definitions,
adding them back in lemmas when they are needed.

## References
* [D. Marcus, *Number Fields*][marcus1977number]
* [J.W.S. Cassels, A. Fröhlich, *Algebraic Number Theory*][cassels1967algebraic]
* [P. Samuel, *Algebraic Theory of Numbers*][samuel1967]

## Tags
function field, ring of integers
-/

noncomputable section

open scoped nonZeroDivisors Polynomial WithZero

variable (F K : Type*) [Field F] [Field K]

abbrev FunctionField [Algebra (RatFunc F) K] : Prop :=
  FiniteDimensional (RatFunc F) K

theorem functionField_iff (Ft : Type*) [Field Ft] [Algebra F[X] Ft]
    [IsFractionRing F[X] Ft] [Algebra (RatFunc F) K] [Algebra Ft K] [Algebra F[X] K]
    [IsScalarTower F[X] Ft K] [IsScalarTower F[X] (RatFunc F) K] :
    FunctionField F K ↔ FiniteDimensional Ft K := by
  let e := IsLocalization.algEquiv F[X]⁰ (RatFunc F) Ft
  have : ∀ (c) (x : K), e c • x = c • x := by
    intro c x
    rw [Algebra.smul_def, Algebra.smul_def]
    congr
    refine congr_fun (f := fun c => algebraMap Ft K (e c)) ?_ c
    refine IsLocalization.ext (nonZeroDivisors F[X]) _ _ ?_ ?_ ?_ ?_ ?_ <;> intros <;>
      simp only [map_one, map_mul, AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]
  constructor <;> intro h
  · let b := Module.finBasis (RatFunc F) K
    exact (b.mapCoeffs e this).finiteDimensional_of_finite
  · let b := Module.finBasis Ft K
    refine (b.mapCoeffs e.symm ?_).finiteDimensional_of_finite
    intro c x; convert (this (e.symm c) x).symm; simp only [e.apply_symm_apply]

namespace FunctionField

theorem algebraMap_injective [Algebra F[X] K] [Algebra (RatFunc F) K]
    [IsScalarTower F[X] (RatFunc F) K] : Function.Injective (⇑(algebraMap F[X] K)) := by
  rw [IsScalarTower.algebraMap_eq F[X] (RatFunc F) K]
  exact (algebraMap (RatFunc F) K).injective.comp (IsFractionRing.injective F[X] (RatFunc F))

def ringOfIntegers [Algebra F[X] K] :=
  integralClosure F[X] K

namespace ringOfIntegers

variable [Algebra F[X] K]

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

variable [Algebra (RatFunc F) K] [IsScalarTower F[X] (RatFunc F) K]

theorem algebraMap_injective : Function.Injective (⇑(algebraMap F[X] (ringOfIntegers F K))) := by
  have hinj : Function.Injective (⇑(algebraMap F[X] K)) := by
    rw [IsScalarTower.algebraMap_eq F[X] (RatFunc F) K]
    exact (algebraMap (RatFunc F) K).injective.comp (IsFractionRing.injective F[X] (RatFunc F))
  rw [injective_iff_map_eq_zero (algebraMap F[X] (↥(ringOfIntegers F K)))]
  intro p hp
  rw [← Subtype.coe_inj, Subalgebra.coe_zero] at hp
  rw [injective_iff_map_eq_zero (algebraMap F[X] K)] at hinj
  exact hinj p hp

theorem not_isField : ¬IsField (ringOfIntegers F K) := by
  simpa [← (IsIntegralClosure.isIntegral_algebra F[X] K).isField_iff_isField
      (algebraMap_injective F K)] using
    Polynomial.not_isField F

variable [FunctionField F K]

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): [Algebra.IsSeparable

-- INSTANCE (free from Core): [Algebra.IsSeparable

end ringOfIntegers

section deprecated
