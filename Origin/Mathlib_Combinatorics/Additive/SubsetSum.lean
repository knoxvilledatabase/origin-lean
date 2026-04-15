/-
Extracted from Combinatorics/Additive/SubsetSum.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Subset sums

This file defines the subset sum of a finite subset of a commutative monoid.

## References

* [Melvyn B. Nathanson, *Inverse theorems for subset sums*][Nathanson1995]
-/

open scoped Pointwise

namespace Finset

variable {M : Type*} [DecidableEq M] [AddCommMonoid M] {A : Finset M} {a : M}

def subsetSum (A : Finset M) : Finset M := A.powerset.image fun B ↦ B.sum id

lemma mem_subsetSum_iff : a ∈ A.subsetSum ↔ ∃ B ⊆ A, ∑ b ∈ B, b = a := by simp [subsetSum]
