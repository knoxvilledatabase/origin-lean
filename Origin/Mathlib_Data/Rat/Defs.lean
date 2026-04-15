/-
Extracted from Data/Rat/Defs.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Basics for the Rational Numbers

## Summary

We define the integral domain structure on `ℚ` and prove basic lemmas about it.
The definition of the field structure on `ℚ` will be done in `Mathlib/Algebra/Field/Rat.lean`
once the `Field` class has been defined.

## Main Definitions

- `Rat.divInt n d` constructs a rational number `q = n / d` from `n d : ℤ`.

## Notation

- `/.` is infix notation for `Rat.divInt`.

-/

assert_not_exists MonoidWithZero Lattice PNat Nat.gcd_greatest

open Function

namespace Rat

variable {q : ℚ}

theorem pos (a : ℚ) : 0 < a.den := Nat.pos_of_ne_zero a.den_nz
