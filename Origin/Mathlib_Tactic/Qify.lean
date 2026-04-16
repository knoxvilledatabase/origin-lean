/-
Extracted from Tactic/Qify.lean
Genuine: 4 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Algebra.Order.Ring.Cast
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Zify

noncomputable section

/-!
# `qify` tactic

The `qify` tactic is used to shift propositions from `ℕ` or `ℤ` to `ℚ`.
This is often useful since `ℚ` has well-behaved division.
```
example (a b c x y z : ℕ) (h : ¬ x*y*z < 0) : c < a + 3*b := by
  qify
  qify at h
  /-
  h : ¬↑x * ↑y * ↑z < 0
  ⊢ ↑c < ↑a + 3 * ↑b
  -/
  sorry
```
-/

namespace Mathlib.Tactic.Qify

open Lean

open Lean.Meta

open Lean.Parser.Tactic

open Lean.Elab.Tactic

syntax (name := qify) "qify" (simpArgs)? (location)? : tactic

macro_rules

| `(tactic| qify $[[$simpArgs,*]]? $[at $location]?) =>

  let args := simpArgs.map (·.getElems) |>.getD #[]

  `(tactic|

    simp -decide only [zify_simps, qify_simps, push_cast, $args,*]

      $[at $location]?)

@[qify_simps] lemma intCast_eq (a b : ℤ) : a = b ↔ (a : ℚ) = (b : ℚ) := by simp only [Int.cast_inj]

@[qify_simps] lemma intCast_le (a b : ℤ) : a ≤ b ↔ (a : ℚ) ≤ (b : ℚ) := Int.cast_le.symm

@[qify_simps] lemma intCast_lt (a b : ℤ) : a < b ↔ (a : ℚ) < (b : ℚ) := Int.cast_lt.symm

@[qify_simps] lemma intCast_ne (a b : ℤ) : a ≠ b ↔ (a : ℚ) ≠ (b : ℚ) := by
  simp only [ne_eq, Int.cast_inj]

alias int_cast_ne := intCast_ne

end Qify

end Mathlib.Tactic
