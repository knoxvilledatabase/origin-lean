/-
Extracted from Topology/MetricSpace/CoveringNumbers.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Covering numbers

We define covering numbers of sets in a pseudo-metric space, which are minimal cardinalities of
`ε`-covers of sets by closed balls.
We also define the packing number, which is the maximal cardinality of an `ε`-separated set.

We prove inequalities between these covering and packing numbers.

## Main definitions

* `externalCoveringNumber`: the external covering number of a set `A` for radius `ε` is the minimal
  cardinality (in `ℕ∞`) of an `ε`-cover.
* `coveringNumber`: the covering number (or internal covering number) of a set `A` for radius `ε` is
  the minimal cardinality (in `ℕ∞`) of an `ε`-cover contained in `A`.
* `packingNumber`: the packing number of a set `A` for radius `ε` is the maximal cardinality of
  an `ε`-separated set in `A`.

We define sets achieving these minimal/maximal cardinalities when they exist:
* `minimalCover`: a finite internal `ε`-cover of a set `A` by closed balls with minimal cardinality.
* `maximalSeparatedSet`: a finite `ε`-separated subset of a set `A` with maximal cardinality.

## Main statements

We have the following inequalities between covering and packing numbers:
* `externalCoveringNumber_le_coveringNumber`: external covering number ≤ covering number.
* `packingNumber_two_mul_le_externalCoveringNumber`: packing number for `2 * ε` ≤ external covering
  number for `ε`.
* `coveringNumber_le_packingNumber`: covering number ≤ packing number.
* `coveringNumber_two_mul_le_externalCoveringNumber`: covering number for `2 * ε` ≤ external
  covering number for `ε`.

The covering number is not monotone for set inclusion (because the cover must be contained
in the set), but we have the following inequality:
* `coveringNumber_subset_le`: if `A ⊆ B`, then `coveringNumber ε A ≤ coveringNumber (ε / 2) B`.

## References

* [R. Vershynin, *High-dimensional probability*][vershynin2018high]

-/

open EMetric Set

open scoped ENNReal NNReal

namespace Metric

variable {X Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y]
  {A B C : Set X} {ε δ : ℝ≥0} {x : X}

section Definitions

noncomputable

def externalCoveringNumber (ε : ℝ≥0) (A : Set X) : ℕ∞ :=
  ⨅ (C : Set X) (_ : IsCover ε A C), C.encard

noncomputable

def coveringNumber (ε : ℝ≥0) (A : Set X) : ℕ∞ :=
  ⨅ (C : Set X) (_ : C ⊆ A) (_ : IsCover ε A C), C.encard

noncomputable

def packingNumber (ε : ℝ≥0) (A : Set X) : ℕ∞ :=
  ⨆ (C : Set X) (_ : C ⊆ A) (_ : IsSeparated ε C), C.encard

end Definitions
