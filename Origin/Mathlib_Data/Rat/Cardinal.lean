/-
Extracted from Data/Rat/Cardinal.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Cardinality of ℚ

This file proves that the Cardinality of ℚ is ℵ₀
-/

assert_not_exists Module Field

open Cardinal

theorem Cardinal.mkRat : #ℚ = ℵ₀ := mk_eq_aleph0 ℚ
