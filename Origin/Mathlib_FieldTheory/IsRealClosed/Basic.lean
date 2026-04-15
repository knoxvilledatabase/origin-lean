/-
Extracted from FieldTheory/IsRealClosed/Basic.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Real Closed Field

A field `R` is real closed if all of the following hold:
1. `R` is real (that is, `-1` is not a sum of squares in `R`).
2. for every `x` in `R`, one of `x` or `-x` is a square.
3. every odd-degree polynomial over `R` has a root in `R`.

A real closed field is an algebraic generalisation of the real numbers.

In this file we define real closed fields and prove some of their properties.

TODO (Artie Khovanov) : equivalent conditions for a real field to be real closed
TODO (Artie Khovanov) : real numbers, real algebraic numbers, hyperreals form a real closed field

## Main Definitions

- `IsRealClosed R` is the typeclass saying `R` is a real closed field.

## Tags

real closed, rcf

-/

open Polynomial

class IsRealClosed (R : Type*) [Field R] : Prop extends IsSemireal R where
  isSquare_or_isSquare_neg (x : R) : IsSquare x ∨ IsSquare (-x)
  exists_isRoot_of_odd_natDegree {f : R[X]} (hf : Odd f.natDegree) : ∃ x, f.IsRoot x

attribute [aesop 90% forward] IsRealClosed.isSquare_or_isSquare_neg

namespace IsRealClosed

universe u

variable {R : Type u} [Field R]

theorem of_linearOrderedField [LinearOrder R] [IsStrictOrderedRing R]
    (isSquare_of_nonneg : ∀ {x : R}, 0 ≤ x → IsSquare x)
    (exists_isRoot_of_odd_natDegree : ∀ {f : R[X]}, Odd f.natDegree → ∃ x, f.IsRoot x) :
    IsRealClosed R where
  isSquare_or_isSquare_neg {x} := by
    rcases le_total x 0 with (neg | pos)
    · exact .inr <| isSquare_of_nonneg (neg_nonneg_of_nonpos neg)
    · exact .inl <| isSquare_of_nonneg pos
  exists_isRoot_of_odd_natDegree := exists_isRoot_of_odd_natDegree

variable [IsRealClosed R]
