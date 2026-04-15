/-
Extracted from RingTheory/ClassGroup.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The ideal class group

This file defines the ideal class group `ClassGroup R` of fractional ideals of `R`
inside its field of fractions.

## Main definitions

- `toPrincipalIdeal` sends an invertible `x : K` to an invertible fractional ideal
- `ClassGroup` is the quotient of invertible fractional ideals modulo `toPrincipalIdeal.range`
- `ClassGroup.mk0` sends a nonzero integral ideal in a Dedekind domain to its class

## Main results
- `ClassGroup.mk0_eq_mk0_iff` shows the equivalence with the "classical" definition,
  where `I ~ J` iff `x I = y J` for `x y ≠ (0 : R)`

## Implementation details

The definition of `ClassGroup R` involves `FractionRing R`. However, the API should be completely
identical no matter the choice of field of fractions for `R`.
-/

variable {R K : Type*} [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]

open scoped nonZeroDivisors

open IsLocalization IsFractionRing FractionalIdeal Units

variable (R K)

irreducible_def toPrincipalIdeal : Kˣ →* (FractionalIdeal R⁰ K)ˣ :=
  { toFun := fun x =>
      ⟨spanSingleton _ x, spanSingleton _ x⁻¹, by
        simp only [spanSingleton_one, Units.mul_inv', spanSingleton_mul_spanSingleton], by
        simp only [spanSingleton_one, Units.inv_mul', spanSingleton_mul_spanSingleton]⟩
    map_mul' := fun x y =>
      ext (by simp only [Units.val_mul, spanSingleton_mul_spanSingleton])
    map_one' := ext (by simp only [spanSingleton_one, Units.val_one]) }

variable {R K}
