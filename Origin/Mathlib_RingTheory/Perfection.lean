/-
Extracted from RingTheory/Perfection.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Ring Perfection and Tilt

In this file we define the perfection of a ring of characteristic p, and the tilt of a field
given a valuation to `ℝ≥0`.

## TODO

Define the valuation on the tilt, and define a characteristic predicate for the tilt.

-/

universe u₁ u₂ u₃ u₄

open scoped NNReal

def Perfection (α : Type u₁) [Pow α ℕ] (p : ℕ) : Type u₁ :=
  { f : ℕ → α // ∀ n, f (n + 1) ^ p = f n }
