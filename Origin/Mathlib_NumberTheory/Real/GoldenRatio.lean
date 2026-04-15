/-
Extracted from NumberTheory/Real/GoldenRatio.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The golden ratio and its conjugate

This file defines the golden ratio `φ := (1 + √5)/2` and its conjugate
`ψ := (1 - √5)/2`, which are the two real roots of `X² - X - 1`.

Along with various computational facts about them, we prove their
irrationality, and we link them to the Fibonacci sequence by proving
Binet's formula.
-/

noncomputable section

open Polynomial

namespace Real

abbrev goldenRatio : ℝ := (1 + √5) / 2

abbrev goldenConj : ℝ := (1 - √5) / 2
