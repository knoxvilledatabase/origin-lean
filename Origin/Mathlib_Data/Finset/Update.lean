/-
Extracted from Data/Finset/Update.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Update a function on a set of values

This file defines `Function.updateFinset`, the operation that updates a function on a
(finite) set of values.

This is a very specific function used for `MeasureTheory.marginal`, and possibly not that useful
for other purposes.
-/

variable {ι : Sort _} {π : ι → Sort _} {x : ∀ i, π i} [DecidableEq ι]
  {s t : Finset ι} {y : ∀ i : s, π i} {z : ∀ i : t, π i} {i : ι}

namespace Function

def updateFinset (x : ∀ i, π i) (s : Finset ι) (y : ∀ i : ↥s, π i) (i : ι) : π i :=
  if hi : i ∈ s then y ⟨i, hi⟩ else x i

open Finset Equiv
