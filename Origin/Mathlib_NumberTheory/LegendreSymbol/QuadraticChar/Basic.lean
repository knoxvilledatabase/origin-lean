/-
Extracted from NumberTheory/LegendreSymbol/QuadraticChar/Basic.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Quadratic characters of finite fields

This file defines the quadratic character on a finite field `F` and proves
some basic statements about it.

## Tags

quadratic character
-/

/-!
### Definition of the quadratic character

We define the quadratic character of a finite field `F` with values in ℤ.
-/

section Define

def quadraticCharFun (α : Type*) [MonoidWithZero α] [DecidableEq α]
    [DecidablePred (IsSquare : α → Prop)] (a : α) : ℤ :=
  if a = 0 then 0 else if IsSquare a then 1 else -1

end Define

/-!
### Basic properties of the quadratic character

We prove some properties of the quadratic character.
We work with a finite field `F` here.
The interesting case is when the characteristic of `F` is odd.
-/

section quadraticChar

open MulChar

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem quadraticCharFun_eq_zero_iff {a : F} : quadraticCharFun F a = 0 ↔ a = 0 := by
  simp only [quadraticCharFun]
  grind
