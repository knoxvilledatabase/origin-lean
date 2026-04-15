/-
Extracted from Analysis/BoxIntegral/Partition/Basic.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Partitions of rectangular boxes in `ℝⁿ`

In this file we define (pre)partitions of rectangular boxes in `ℝⁿ`. A partition of a box `I` in
`ℝⁿ` (see `BoxIntegral.Prepartition` and `BoxIntegral.Prepartition.IsPartition`) is a finite set
of pairwise disjoint boxes such that their union is exactly `I`. We use `boxes : Finset (Box ι)` to
store the set of boxes.

Many lemmas about box integrals deal with pairwise disjoint collections of subboxes, so we define a
structure `BoxIntegral.Prepartition (I : BoxIntegral.Box ι)` that stores a collection of boxes
such that

* each box `J ∈ boxes` is a subbox of `I`;
* the boxes are pairwise disjoint as sets in `ℝⁿ`.

Then we define a predicate `BoxIntegral.Prepartition.IsPartition`; `π.IsPartition` means that the
boxes of `π` actually cover the whole `I`. We also define some operations on prepartitions:

* `BoxIntegral.Prepartition.biUnion`: split each box of a partition into smaller boxes;
* `BoxIntegral.Prepartition.restrict`: restrict a partition to a smaller box.

We also define a `SemilatticeInf` structure on `BoxIntegral.Prepartition I` for all
`I : BoxIntegral.Box ι`.

## Tags

rectangular box, partition
-/

open Set Finset Function

open scoped NNReal

noncomputable section

namespace BoxIntegral

variable {ι : Type*}

structure Prepartition (I : Box ι) where
  /-- The underlying set of boxes -/
  boxes : Finset (Box ι)
  /-- Each box is a sub-box of `I` -/
  le_of_mem' : ∀ J ∈ boxes, J ≤ I
  /-- The boxes in a prepartition are pairwise disjoint. -/
  pairwiseDisjoint : Set.Pairwise (↑boxes) (Disjoint on ((↑) : Box ι → Set (ι → ℝ)))

namespace Prepartition

variable {I J J₁ J₂ : Box ι} (π : Prepartition I) {π₁ π₂ : Prepartition I} {x : ι → ℝ}

-- INSTANCE (free from Core): :
