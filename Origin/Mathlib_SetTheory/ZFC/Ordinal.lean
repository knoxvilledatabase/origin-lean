/-
Extracted from SetTheory/ZFC/Ordinal.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Von Neumann ordinals

This file works towards the development of von Neumann ordinals, i.e. transitive sets, well-ordered
under `∈`.

## Definitions

- `ZFSet.IsTransitive` means that every element of a set is a subset.
- `ZFSet.IsOrdinal` means that the set is transitive and well-ordered under `∈`. We show multiple
  equivalences to this definition.
- `Ordinal.toZFSet` converts Lean's type-theoretic ordinals into ZFC ordinals. We prove that these
  two notions are order-isomorphic.
-/

universe u

variable {x y z w : ZFSet.{u}}

open Set

namespace ZFSet

/-! ### Transitive sets -/

def IsTransitive (x : ZFSet) : Prop :=
  ∀ y ∈ x, y ⊆ x
