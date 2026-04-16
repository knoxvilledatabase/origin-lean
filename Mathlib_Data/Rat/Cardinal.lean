/-
Extracted from Data/Rat/Cardinal.lean
Genuine: 1 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Ring.Rat
import Mathlib.Data.Rat.Encodable
import Mathlib.SetTheory.Cardinal.Basic

noncomputable section

/-!
# Cardinality of ℚ

This file proves that the Cardinality of ℚ is ℵ₀
-/

open Cardinal

theorem Cardinal.mkRat : #ℚ = ℵ₀ := mk_eq_aleph0 ℚ
