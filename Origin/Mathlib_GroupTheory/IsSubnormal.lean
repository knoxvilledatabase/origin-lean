/-
Extracted from GroupTheory/IsSubnormal.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Subnormal subgroups

In this file, we define subnormal subgroups.

We also show some basic results about the interaction of subnormality and simplicity of groups.
These should cover most of the results needed in this case.

## Main Definition

`IsSubnormal H`: A subgroup `H` of a group `G` satisfies `IsSubnormal` if
* either `H = ⊤`;
* or there is a subgroup `K` of `G` containing `H` and such that `H` is normal in `K` and
  `K` satisfies `IsSubnormal`.

## Main Statements

* `eq_bot_or_top_of_isSimpleGroup`: the only subnormal subgroups of simple groups are
  `⊥`, the trivial subgroup, and `⊤`, the whole group.
* `isSubnormal_iff`: Shows that `IsSubnormal H` holds if and only if there is
  an increasing chain of subgroups, each normal in the following, starting from `H` and
  reaching `⊤` in a finite number of steps.
* `IsSubnormal.trans`: The relation of being `IsSubnormal` is transitive.

## Implementation Notes

We deviate from the common informal definition of subnormality and use an inductive predicate.
This turns out to be more convenient to work with.
We show the equivalence of the current definition with the existence of chains in
`isSubnormal_iff`.
-/

variable {G : Type*} [Group G] {H K : Subgroup G}

namespace Subgroup

inductive IsSubnormal : Subgroup G → Prop where
  /-- The whole subgroup `G` is subnormal in itself. -/
  | top : IsSubnormal (⊤ : Subgroup G)
  /-- A subgroup `H` is subnormal if there is a subnormal subgroup `K` containing `H` that is
  subnormal itself and such that `H` is normal in `K`. -/
  | step : ∀ H K, (h_le : H ≤ K) → (hSubn : IsSubnormal K) → (hN : (H.subgroupOf K).Normal) →
    IsSubnormal H

inductive _root_.AddSubgroup.IsSubnormal {G : Type*} [AddGroup G] : AddSubgroup G → Prop where
  /-- The whole additive subgroup `G` is subnormal in itself. -/
  | top : IsSubnormal (⊤ : AddSubgroup G)
  /-- An additive subgroup `H` is subnormal if there is a subnormal additive subgroup `K`
  containing `H` that is subnormal itself and such that `H` is normal in `K`. -/
  | step : ∀ H K, (h_le : H ≤ K) → (hSubn : IsSubnormal K) → (hN : (H.addSubgroupOf K).Normal) →
    IsSubnormal H

attribute [simp] Subgroup.IsSubnormal.top
