/-
Extracted from RingTheory/Valuation/AlgebraInstances.lean
Genuine: 5 of 8 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Algebra instances

This file contains several `Algebra` and `IsScalarTower` instances related to extensions
of a field with a valuation, as well as their unit balls.

## Main definitions
* `ValuationSubring.algebra` : Given an algebra between two field extensions `L` and `E` of a
  field `K` with a valuation, create an algebra between their two rings of integers.

## Main statements

* `integralClosure_algebraMap_injective` : the unit ball of a field `K` with respect to a
  valuation injects into its integral closure in a field extension `L` of `K`.
-/

open Function Valuation

open scoped WithZero

variable {K : Type*} [Field K] (v : Valuation K ℤᵐ⁰) (L : Type*) [Field L] [Algebra K L]

namespace ValuationSubring

-- INSTANCE (free from Core): :

theorem algebraMap_injective : Injective (algebraMap v.valuationSubring L) :=
  (FaithfulSMul.algebraMap_injective K L).comp (IsFractionRing.injective _ _)

theorem isIntegral_of_mem_ringOfIntegers {x : L} (hx : x ∈ integralClosure v.valuationSubring L) :
    IsIntegral v.valuationSubring (⟨x, hx⟩ : integralClosure v.valuationSubring L) :=
  integralClosure.isIntegral ⟨x, hx⟩

theorem isIntegral_of_mem_ringOfIntegers' {x : integralClosure v.valuationSubring L} :
    IsIntegral v.valuationSubring (x : integralClosure v.valuationSubring L) := by
  apply isIntegral_of_mem_ringOfIntegers

variable (E : Type _) [Field E] [Algebra K E] [Algebra L E] [IsScalarTower K L E]

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): algebra

protected noncomputable def equiv (R : Type*) [CommRing R] [Algebra v.valuationSubring R]
    [Algebra R L] [IsScalarTower v.valuationSubring R L]
    [IsIntegralClosure R v.valuationSubring L] : integralClosure v.valuationSubring L ≃+* R :=
  (IsIntegralClosure.equiv v.valuationSubring R L
    (integralClosure v.valuationSubring L)).symm.toRingEquiv

theorem integralClosure_algebraMap_injective :
    Injective (algebraMap v.valuationSubring (integralClosure v.valuationSubring L)) :=
  FaithfulSMul.algebraMap_injective ..

end ValuationSubring
