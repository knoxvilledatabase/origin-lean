/-
Extracted from Data/ENNReal/Real.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Maps between real and extended non-negative real numbers

This file focuses on the functions `ENNReal.toReal : ℝ≥0∞ → ℝ` and `ENNReal.ofReal : ℝ → ℝ≥0∞` which
were defined in `Data.ENNReal.Basic`. It collects all the basic results of the interactions between
these functions and the algebraic and lattice operations, although a few may appear in earlier
files.

This file provides a `positivity` extension for `ENNReal.ofReal`.

## Main statements

  - `trichotomy (p : ℝ≥0∞) : p = 0 ∨ p = ∞ ∨ 0 < p.toReal`: often used for `WithLp` and `lp`
  - `dichotomy (p : ℝ≥0∞) [Fact (1 ≤ p)] : p = ∞ ∨ 1 ≤ p.toReal`: often used for `WithLp` and `lp`
  - `toNNReal_iInf` through `toReal_sSup`: these declarations allow for easy conversions between
    indexed or set infima and suprema in `ℝ`, `ℝ≥0` and `ℝ≥0∞`. This is especially useful because
    `ℝ≥0∞` is a complete lattice.
-/

assert_not_exists Finset

open Set NNReal ENNReal

namespace ENNReal

section Real

variable {a b c d : ℝ≥0∞} {r p q : ℝ≥0}

theorem toReal_add (ha : a ≠ ∞) (hb : b ≠ ∞) : (a + b).toReal = a.toReal + b.toReal := by
  lift a to ℝ≥0 using ha
  lift b to ℝ≥0 using hb
  rfl

theorem toReal_add_le : (a + b).toReal ≤ a.toReal + b.toReal :=
  if ha : a = ∞ then by simp only [ha, top_add, toReal_top, zero_add, toReal_nonneg]
  else
    if hb : b = ∞ then by simp only [hb, add_top, toReal_top, add_zero, toReal_nonneg]
    else le_of_eq (toReal_add ha hb)

theorem ofReal_add {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    ENNReal.ofReal (p + q) = ENNReal.ofReal p + ENNReal.ofReal q := by
  rw [ENNReal.ofReal, ENNReal.ofReal, ENNReal.ofReal, ← coe_add, coe_inj,
    Real.toNNReal_add hp hq]

theorem ofReal_add_le {p q : ℝ} : ENNReal.ofReal (p + q) ≤ ENNReal.ofReal p + ENNReal.ofReal q :=
  coe_le_coe.2 Real.toNNReal_add_le
