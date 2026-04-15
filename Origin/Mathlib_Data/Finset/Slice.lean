/-
Extracted from Data/Finset/Slice.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# `r`-sets and slice

This file defines the `r`-th slice of a set family and provides a way to say that a set family is
made of `r`-sets.

An `r`-set is a finset of cardinality `r` (aka of *size* `r`). The `r`-th slice of a set family is
the set family made of its `r`-sets.

## Main declarations

* `Set.Sized`: `A.Sized r` means that `A` only contains `r`-sets.
* `Finset.slice`: `A.slice r` is the set of `r`-sets in `A`.

## Notation

`A # r` is notation for `A.slice r` in scope `finset_family`.
-/

open Finset Nat

variable {α : Type*} {ι : Sort*} {κ : ι → Sort*}

namespace Set

variable {A B : Set (Finset α)} {s : Finset α} {r : ℕ}

/-! ### Families of `r`-sets -/

def Sized (r : ℕ) (A : Set (Finset α)) : Prop := ∀ ⦃x⦄, x ∈ A → #x = r

theorem Sized.mono (h : A ⊆ B) (hB : B.Sized r) : A.Sized r := fun _x hx => hB <| h hx
