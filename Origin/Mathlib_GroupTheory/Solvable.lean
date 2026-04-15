/-
Extracted from GroupTheory/Solvable.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Solvable Groups

In this file we introduce the notion of a solvable group. We define a solvable group as one whose
derived series is eventually trivial. This requires defining the commutator of two subgroups and
the derived series of a group.

## Main definitions

* `derivedSeries G n` : the `n`th term in the derived series of `G`, defined by iterating
    `general_commutator` starting with the top subgroup
* `IsSolvable G` : the group `G` is solvable
-/

open Subgroup

open scoped commutatorElement

variable {G G' : Type*} [Group G] [Group G'] {f : G →* G'}

section derivedSeries

variable (G)

def derivedSeries : ℕ → Subgroup G
  | 0 => ⊤
  | n + 1 => ⁅derivedSeries n, derivedSeries n⁆
