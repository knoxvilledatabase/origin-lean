/-
Extracted from Combinatorics/Matroid/Constructions.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Some constructions of matroids

This file defines some very elementary examples of matroids, namely those with at most one base.

## Main definitions

* `emptyOn α` is the matroid on `α` with empty ground set.

For `E : Set α`, ...

* `loopyOn E` is the matroid on `E` whose elements are all loops, or equivalently in which `∅`
  is the only base.
* `freeOn E` is the 'free matroid' whose ground set `E` is the only base.
* For `I ⊆ E`, `uniqueBaseOn I E` is the matroid with ground set `E` in which `I` is the only base.

## Implementation details

To avoid the tedious process of certifying the matroid axioms for each of these easy examples,
we bootstrap the definitions starting with `emptyOn α` (which `simp` can prove is a matroid)
and then construct the other examples using duality and restriction.

-/

assert_not_exists Field

variable {α : Type*} {M : Matroid α} {E B I X R J : Set α}

namespace Matroid

open Set

section EmptyOn

def emptyOn (α : Type*) : Matroid α where
  E := ∅
  IsBase := (· = ∅)
  Indep := (· = ∅)
  indep_iff' := by simp [subset_empty_iff]
  exists_isBase := ⟨∅, rfl⟩
  isBase_exchange := by rintro _ _ rfl; simp
  maximality := by rintro _ _ _ rfl -; exact ⟨∅, by simp [Maximal]⟩
  subset_ground := by simp
