/-
Extracted from Data/Finset/Piecewise.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Functions defined piecewise on a finset

This file defines `Finset.piecewise`: Given two functions `f`, `g`, `s.piecewise f g` is a function
which is equal to `f` on `s` and `g` on the complement.

## TODO

Should we deduplicate this from `Set.piecewise`?
-/

open Function

namespace Finset

variable {ι : Type*} {π : ι → Sort*} (s : Finset ι) (f g : ∀ i, π i)

def piecewise [∀ j, Decidable (j ∈ s)] : ∀ i, π i := fun i ↦ if i ∈ s then f i else g i

lemma piecewise_insert_self [DecidableEq ι] {j : ι} [∀ i, Decidable (i ∈ insert j s)] :
    (insert j s).piecewise f g j = f j := by simp [piecewise]
