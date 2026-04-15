/-
Extracted from Data/Complex/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The complex numbers

The complex numbers are modelled as ℝ^2 in the obvious way and it is shown that they form a field
of characteristic zero. For the result that the complex numbers are algebraically closed, see
`Complex.isAlgClosed` in `Mathlib.Analysis.Complex.Polynomial.Basic`.
-/

assert_not_exists Multiset Algebra

open Set Function

/-! ### Definition and basic arithmetic -/

structure Complex : Type where
  /-- The real part of a complex number. -/
  re : ℝ
  /-- The imaginary part of a complex number. -/
  im : ℝ
