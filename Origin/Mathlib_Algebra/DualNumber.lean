/-
Extracted from Algebra/DualNumber.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Dual numbers

The dual numbers over `R` are of the form `a + bε`, where `a` and `b` are typically elements of a
commutative ring `R`, and `ε` is a symbol satisfying `ε^2 = 0` that commutes with every other
element. They are a special case of `TrivSqZeroExt R M` with `M = R`.

## Notation

In the `DualNumber` locale:

* `R[ε]` is a shorthand for `DualNumber R`
* `ε` is a shorthand for `DualNumber.eps`

## Main definitions

* `DualNumber`
* `DualNumber.eps`
* `DualNumber.lift`

## Implementation notes

Rather than duplicating the API of `TrivSqZeroExt`, this file reuses the functions there.

## References

* https://en.wikipedia.org/wiki/Dual_number
-/

variable {R A B : Type*}

abbrev DualNumber (R : Type*) : Type _ :=
  TrivSqZeroExt R R

def DualNumber.eps [Zero R] [One R] : DualNumber R :=
  TrivSqZeroExt.inr 1
