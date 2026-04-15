/-
Extracted from NumberTheory/MahlerMeasure.lean
Genuine: 2 of 3 | Dissolved: 1 | Infrastructure: 0
-/
import Origin.Core

/-!
# Mahler measure of integer polynomials

The main purpose of this file is to prove some facts about the Mahler measure of integer
polynomials, in particular Northcott's Theorem for the Mahler measure.

## Main results
- `Polynomial.finite_mahlerMeasure_le`: Northcott's Theorem: the set of integer polynomials of
  degree at most `n` and Mahler measure at most `B` is finite.
- `Polynomial.card_mahlerMeasure_le_prod`: an upper bound on the number of integer polynomials
  of degree at most `n` and Mahler measure at most `B`.
- `Polynomial.cyclotomic_mahlerMeasure_eq_one`: the Mahler measure of a cyclotomic polynomial is 1.
- `Polynomial.pow_eq_one_of_mahlerMeasure_eq_one`: if an integer polynomial has Mahler measure equal
  to 1, then all its complex nonzero roots are roots of unity.
- `Polynomial.cyclotomic_dvd_of_mahlerMeasure_eq_one`: if an integer non-constant polynomial has
  Mahler measure equal to 1 and is not a multiple of X, then it is divisible by a cyclotomic
  polynomial.
-/

namespace Polynomial

open Int

-- DISSOLVED: one_le_mahlerMeasure_of_ne_zero

section Northcott

variable (n : ℕ) (B₁ B₂ : Fin (n + 1) → ℝ)

def boxPoly : Set ℤ[X] := {p : ℤ[X] | p.natDegree ≤ n ∧ ∀ i, B₁ i ≤ p.coeff i ∧ p.coeff i ≤ B₂ i}

theorem ncard_boxPoly : (boxPoly n B₁ B₂).ncard = ∏ i, (⌊B₂ i⌋ - ⌈B₁ i⌉ + 1).toNat := by
  trans Set.ncard (α := Fin (n + 1) → ℤ) (Finset.Icc (⌈B₁ ·⌉) (⌊B₂ ·⌋))
  · refine Set.ncard_congr' ⟨fun p ↦ ⟨toFn (n + 1) p, ?_⟩, fun p ↦ ⟨ofFn (n + 1) p, ?_⟩, ?_, ?_⟩
    · have prop := p.property.2
      simpa using ⟨fun i ↦ ceil_le.mpr (prop i).1, fun i ↦ le_floor.mpr (prop i).2⟩
    · refine ⟨Nat.le_of_lt_succ <| ofFn_natDegree_lt (Nat.le_add_left 1 n) p.val, fun i ↦ ?_⟩
      have prop := Finset.mem_Icc.mp p.property
      rw [ofFn_coeff_eq_val_of_lt _ i.2]
      exact ⟨ceil_le.mp (prop.1 i), le_floor.mp (prop.2 i)⟩
    · grind [boxPoly, ofFn_comp_toFn_eq_id_of_natDegree_lt]
    · grind [toFn_comp_ofFn_eq_id]
  · norm_cast
    grind [Pi.card_Icc, card_Icc]
