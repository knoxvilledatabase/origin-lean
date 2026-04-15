/-
Extracted from Combinatorics/SimpleGraph/Regularity/Bound.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Numerical bounds for Szemerédi Regularity Lemma

This file gathers the numerical facts required by the proof of Szemerédi's regularity lemma.

This entire file is internal to the proof of Szemerédi Regularity Lemma.

## Main declarations

* `SzemerediRegularity.stepBound`: During the inductive step, a partition of size `n` is blown to
  size at most `stepBound n`.
* `SzemerediRegularity.initialBound`: The size of the partition we start the induction with.
* `SzemerediRegularity.bound`: The upper bound on the size of the partition produced by our version
  of Szemerédi's regularity lemma.

## References

[Yaël Dillies, Bhavik Mehta, *Formalising Szemerédi’s Regularity Lemma in Lean*][srl_itp]
-/

open Finset Fintype Function Real

namespace SzemerediRegularity

def stepBound (n : ℕ) : ℕ :=
  n * 4 ^ n

theorem le_stepBound : id ≤ stepBound := fun n =>
  Nat.le_mul_of_pos_right _ <| pow_pos (by simp) n

theorem stepBound_mono : Monotone stepBound := fun _ _ h => by unfold stepBound; gcongr; decide

theorem stepBound_pos_iff {n : ℕ} : 0 < stepBound n ↔ 0 < n :=
  mul_pos_iff_of_pos_right <| by positivity

alias ⟨_, stepBound_pos⟩ := stepBound_pos_iff
