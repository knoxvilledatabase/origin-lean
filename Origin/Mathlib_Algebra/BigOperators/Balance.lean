/-
Extracted from Algebra/BigOperators/Balance.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Balancing a function

This file defines the balancing of a function `f`, defined as `f` minus its average.

This is the unique function `g` such that `f a - f b = g a - g b` for all `a` and `b`, and
`∑ a, g a = 0`. This is particularly useful in Fourier analysis as `f` and `g` then have the same
Fourier transform, except in the `0`-th frequency where the Fourier transform of `g` vanishes.
-/

open Finset Function

open scoped BigOperators

variable {ι H F G : Type*}

namespace Fintype

section AddCommGroup

variable [Fintype ι] [AddCommGroup G] [Module ℚ≥0 G] [AddCommGroup H] [Module ℚ≥0 H]

def balance (f : ι → G) : ι → G := f - Function.const _ (𝔼 y, f y)
