/-
Extracted from NumberTheory/Zsqrtd/GaussianInt.lean
Genuine: 4 of 8 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# Gaussian integers

The Gaussian integers are complex integer, complex numbers whose real and imaginary parts are both
integers.

## Main definitions

The Euclidean domain structure on `ℤ[i]` is defined in this file.

The homomorphism `GaussianInt.toComplex` into the complex numbers is also defined in this file.

## See also

See `NumberTheory.Zsqrtd.QuadraticReciprocity` for:
* `prime_iff_mod_four_eq_three_of_nat_prime`:
  A prime natural number is prime in `ℤ[i]` if and only if it is `3` mod `4`

## Notation

This file uses the local notation `ℤ[i]` for `GaussianInt`

## Implementation notes

Gaussian integers are implemented using the more general definition `Zsqrtd`, the type of integers
adjoined a square root of `d`, in this case `-1`. The definition is reducible, so that properties
and definitions about `Zsqrtd` can easily be used.
-/

open Zsqrtd Complex

open scoped ComplexConjugate

abbrev GaussianInt : Type :=
  Zsqrtd (-1)

local notation "ℤ[i]" => GaussianInt

namespace GaussianInt

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): instCommRing

attribute [-instance] Complex.instField -- Avoid making things noncomputable unnecessarily.

def toComplex : ℤ[i] →+* ℂ :=
  Zsqrtd.lift ⟨I, by simp⟩

end

-- INSTANCE (free from Core): :

theorem toComplex_def' (x y : ℤ) : ((⟨x, y⟩ : ℤ[i]) : ℂ) = x + y * I := by simp [toComplex_def]

theorem toComplex_def₂ (x : ℤ[i]) : (x : ℂ) = ⟨x.re, x.im⟩ := by
  apply Complex.ext <;> simp [toComplex_def]
