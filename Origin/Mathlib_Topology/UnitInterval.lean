/-
Extracted from Topology/UnitInterval.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The unit interval, as a topological space

Use `open unitInterval` to turn on the notation `I := Set.Icc (0 : ℝ) (1 : ℝ)`.

We provide basic instances, as well as a custom tactic for discharging
`0 ≤ ↑x`, `0 ≤ 1 - ↑x`, `↑x ≤ 1`, and `1 - ↑x ≤ 1` when `x : I`.

-/

noncomputable section

open Topology Filter Set Int Set.Icc

/-! ### The unit interval -/

abbrev unitInterval : Set ℝ :=
  Set.Icc 0 1
