/-
Extracted from Data/Complex/Cardinality.lean
Genuine: 3 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Cardinality

/-!
# The cardinality of the complex numbers

This file shows that the complex numbers have cardinality continuum, i.e. `#ℂ = 𝔠`.
-/

open Cardinal Set

open Cardinal

@[simp]
theorem mk_complex : #ℂ = 𝔠 := by
  rw [mk_congr Complex.equivRealProd, mk_prod, lift_id, mk_real, continuum_mul_self]

theorem mk_univ_complex : #(Set.univ : Set ℂ) = 𝔠 := by rw [mk_univ, mk_complex]

theorem not_countable_complex : ¬(Set.univ : Set ℂ).Countable := by
  rw [← le_aleph0_iff_set_countable, not_le, mk_univ_complex]
  apply cantor
