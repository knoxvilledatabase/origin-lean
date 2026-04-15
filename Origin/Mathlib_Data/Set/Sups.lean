/-
Extracted from Data/Set/Sups.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Set family operations

This file defines a few binary operations on `Set α` for use in set family combinatorics.

## Main declarations

* `s ⊻ t`: Set of elements of the form `a ⊔ b` where `a ∈ s`, `b ∈ t`.
* `s ⊼ t`: Set of elements of the form `a ⊓ b` where `a ∈ s`, `b ∈ t`.

## Notation

We define the following notation in scope `SetFamily`:
* `s ⊻ t`
* `s ⊼ t`

## References

[B. Bollobás, *Combinatorics*][bollobas1986]
-/

open Function

variable {F α β : Type*}

class HasSups (α : Type*) where
  /-- The point-wise supremum `a ⊔ b` of `a, b : α`. -/
  sups : α → α → α

class HasInfs (α : Type*) where
  /-- The point-wise infimum `a ⊓ b` of `a, b : α`. -/
  infs : α → α → α
