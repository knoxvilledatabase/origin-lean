/-
Extracted from LinearAlgebra/AffineSpace/Slope.lean
Genuine: 3 of 4 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Slope of a function

In this file we define the slope of a function `f : k → PE` taking values in an affine space over
`k` and prove some basic theorems about `slope`. The `slope` function naturally appears in the Mean
Value Theorem, and in the proof of the fact that a function with nonnegative second derivative on an
interval is convex on this interval.

## Tags

affine space, slope
-/

open AffineMap

variable {k E PE : Type*} [Field k] [AddCommGroup E] [Module k E] [AddTorsor E PE]

def slope (f : k → PE) (a b : k) : E :=
  (b - a)⁻¹ • (f b -ᵥ f a)

theorem slope_def_field (f : k → k) (a b : k) : slope f a b = (f b - f a) / (b - a) :=
  (div_eq_inv_mul _ _).symm

theorem slope_fun_def_field (f : k → k) (a : k) : slope f a = fun b => (f b - f a) / (b - a) :=
  (div_eq_inv_mul _ _).symm
