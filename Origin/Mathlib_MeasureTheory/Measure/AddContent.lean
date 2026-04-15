/-
Extracted from MeasureTheory/Measure/AddContent.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Additive Contents

An additive content `m` on a set of sets `C` is a set function with value 0 at the empty set which
is finitely additive on `C`. That means that for any finset `I` of pairwise disjoint sets in `C`
such that `⋃₀ I ∈ C`, `m (⋃₀ I) = ∑ s ∈ I, m s`.

Mathlib also has a definition of contents over compact sets: see `MeasureTheory.Content`.
A `Content` is in particular an `AddContent` on the set of compact sets.

## Main definitions

* `MeasureTheory.AddContent G C`: additive contents over the set of sets `C` taking values in the
  additive monoid `G`.
* `MeasureTheory.AddContent.IsSigmaSubadditive`: an `AddContent` with values in `ℝ≥0∞` is
  σ-subadditive if `m (⋃ i, f i) ≤ ∑' i, m (f i)` for any sequence of sets `f` in `C`
  such that `⋃ i, f i ∈ C`.

## Main statements

Let `m` be an `AddContent C` with values in `ℝ≥0∞`. If `C` is a set semi-ring (`IsSetSemiring C`)
we have the properties

* `MeasureTheory.sum_addContent_le_of_subset`: if `I` is a finset of pairwise disjoint sets in `C`
  and `⋃₀ I ⊆ t` for `t ∈ C`, then `∑ s ∈ I, m s ≤ m t`.
* `MeasureTheory.addContent_mono`: if `s ⊆ t` for two sets in `C`, then `m s ≤ m t`.
* `MeasureTheory.addContent_sUnion_le_sum`: an `AddContent C` on a `SetSemiring C` is
  sub-additive.
* `MeasureTheory.addContent_iUnion_eq_tsum_of_disjoint_of_addContent_iUnion_le`: if an
  `AddContent` is σ-subadditive on a semi-ring of sets, then it is σ-additive.
* `MeasureTheory.addContent_union'`: if `s, t ∈ C` are disjoint and `s ∪ t ∈ C`,
  then `m (s ∪ t) = m s + m t`.
  If `C` is a set ring (`IsSetRing`), then `addContent_union` gives the same conclusion without the
  hypothesis `s ∪ t ∈ C` (since it is a consequence of `IsSetRing C`).

If `C` is a set ring (`MeasureTheory.IsSetRing C`), we have

* `MeasureTheory.addContent_union_le`: for `s, t ∈ C`, `m (s ∪ t) ≤ m s + m t`
* `MeasureTheory.addContent_le_diff`: for `s, t ∈ C`, `m s - m t ≤ m (s \ t)`
* `IsSetRing.addContent_of_union`: a function on a ring of sets which is additive on pairs of
  disjoint sets defines an additive content
* `addContent_iUnion_eq_sum_of_tendsto_zero`: if an additive content is continuous at `∅`, then
  its value on a countable disjoint union is the sum of the values
* `MeasureTheory.isSigmaSubadditive_of_addContent_iUnion_eq_tsum`: if an `AddContent` is
  σ-additive on a set ring, then it is σ-subadditive.

We define a specific example of `AddContent`, called `AddContent.onIoc`, on the semiring of sets
made of open-closed intervals, mapping `(a, b]` to `f b - f a`.
-/

open Set Finset Function Filter

open scoped ENNReal Topology Function

namespace MeasureTheory

variable {α : Type*} {C : Set (Set α)} {s t : Set α} {I : Finset (Set α)}

{G : Type*} [AddCommMonoid G]

variable (G) in

structure AddContent (C : Set (Set α)) where
  /-- The value of the content on a set. -/
  toFun : Set α → G
  empty' : toFun ∅ = 0
  sUnion' (I : Finset (Set α)) (_h_ss : ↑I ⊆ C)
      (_h_dis : PairwiseDisjoint (I : Set (Set α)) id) (_h_mem : ⋃₀ ↑I ∈ C) :
    toFun (⋃₀ I) = ∑ u ∈ I, toFun u

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

variable {m m' : AddContent G C}
