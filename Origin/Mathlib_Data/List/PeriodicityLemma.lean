/-
Extracted from Data/List/PeriodicityLemma.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! # Periods of words (Lists)

This file defines the notion of a period of a word (list) and proves the Periodicity Lemma.

## Implementation notes

The definition of a period is given in terms of self-overlap.
Equivalent characterizations in terms of indices and modular arithmetic are also provided.

## Tags

periodicity lemma, Fine-Wilf theorem, period, periodicity

-/

variable {α : Type _}

open Nat

namespace List

def HasPeriod (w : List α) (p : ℕ) : Prop := w <+: take p w ++ w

lemma hasPeriod_iff_getElem? {p : ℕ} {w : List α} :
    HasPeriod w p ↔ ∀ i < w.length - p, w[i]? = w[i + p]? := by
  constructor
  · rw [HasPeriod]
    intro pref j len
    have i1 : j < w.length := by lia
    have i2 : j + p < w.length := by lia
    have min : p < w.length := by lia
    have : j + p - (List.take p w).length = j := by
      simp_all [min_eq_left_of_lt]
    simp_all [getElem_append_right, IsPrefix.getElem pref, min_eq_left_of_lt]
  · intro lhs
    rw [HasPeriod]
    have drop : drop p w <+: w := by
      simp only [prefix_iff_getElem?, length_drop, getElem_drop]
      intro i leni
      have len : i + p < w.length := by lia
      simp_all only [getElem?_pos, add_comm p i]
    rw [← prefix_append_right_inj (w.take p)] at drop
    simp_all
