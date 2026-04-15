/-
Extracted from FieldTheory/RatFunc/Valuation.lean
Genuine: 5 of 5 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Valuations on F(t)

This file defines the valuation at infinity on the field of rational functions `F(t)`.

## Main definitions

- `RatFunc.inftyValuation` : The place at infinity on `F(t)` is the nonarchimedean
  valuation on `F(t)` with uniformizer `1/t`.
- `RatFunc.CompletionAtInfty` : The completion `F((t⁻¹))` of `F(t)` with respect to the
  valuation at infinity.

## References
* [D. Marcus, *Number Fields*][marcus1977number]
* [J.W.S. Cassels, A. Fröhlich, *Algebraic Number Theory*][cassels1967algebraic]
* [P. Samuel, *Algebraic Theory of Numbers*][samuel1967]

## Tags
function field, ring of integers
-/

public noncomputable section

namespace RatFunc

variable (F K : Type*) [Field F] [Field K]

/-! ### The place at infinity on F(t) -/

section InftyValuation

open Multiplicative WithZero Polynomial

variable [DecidableEq (RatFunc F)]

def inftyValuationDef (r : RatFunc F) : ℤᵐ⁰ :=
  if r = 0 then 0 else exp r.intDegree

theorem InftyValuation.map_zero' : inftyValuationDef F 0 = 0 :=
  if_pos rfl

theorem InftyValuation.map_one' : inftyValuationDef F 1 = 1 :=
  (if_neg one_ne_zero).trans <| by simp

theorem InftyValuation.map_mul' (x y : RatFunc F) :
    inftyValuationDef F (x * y) = inftyValuationDef F x * inftyValuationDef F y := by
  rw [inftyValuationDef, inftyValuationDef, inftyValuationDef]
  by_cases hx : x = 0
  · rw [hx, zero_mul, if_pos (Eq.refl _), zero_mul]
  · by_cases hy : y = 0
    · rw [hy, mul_zero, if_pos (Eq.refl _), mul_zero]
    · simp_all [RatFunc.intDegree_mul]

theorem InftyValuation.map_add_le_max' (x y : RatFunc F) :
    inftyValuationDef F (x + y) ≤ max (inftyValuationDef F x) (inftyValuationDef F y) := by
  by_cases hx : x = 0
  · rw [hx, zero_add]
    conv_rhs => rw [inftyValuationDef, if_pos (Eq.refl _)]
    rw [max_eq_right (WithZero.zero_le (inftyValuationDef F y))]
  · by_cases hy : y = 0
    · rw [hy, add_zero]
      conv_rhs => rw [max_comm, inftyValuationDef, if_pos (Eq.refl _)]
      rw [max_eq_right (WithZero.zero_le (inftyValuationDef F x))]
    · by_cases hxy : x + y = 0
      · rw [inftyValuationDef, if_pos hxy]; exact zero_le'
      · rw [inftyValuationDef, inftyValuationDef, inftyValuationDef, if_neg hx, if_neg hy,
          if_neg hxy]
        simpa using RatFunc.intDegree_add_le hy hxy
