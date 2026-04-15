/-
Extracted from Analysis/BoxIntegral/UnitPartition.lean
Genuine: 2 of 3 | Dissolved: 1 | Infrastructure: 0
-/
import Origin.Core

/-!
# Unit Partition

Fix `n` a positive integer. `BoxIntegral.unitPartition.box` are boxes in `ι → ℝ` obtained by
dividing the unit box uniformly into boxes of side length `1 / n` and translating the boxes by
vectors `ν : ι → ℤ`.

Let `B` be a `BoxIntegral`. A `unitPartition.box` is admissible for `B` (more precisely its index is
admissible) if it is contained in `B`. There are finitely many admissible `unitPartition.box` for
`B` and thus we can form the corresponding tagged prepartition, see
`BoxIntegral.unitPartition.prepartition` (note that each `unitPartition.box` comes with its
tag situated at its "upper most" vertex). If `B` satisfies `hasIntegralVertices`, that
is its vertices are in `ι → ℤ`, then the corresponding prepartition is actually a partition.

## Main definitions and results

* `BoxIntegral.hasIntegralVertices`: a `Prop` that states that the vertices of the box have
  coordinates in `ℤ`

* `BoxIntegral.unitPartition.box`: a `BoxIntegral`, indexed by `ν : ι → ℤ`, with vertices
  `ν i / n` and of side length `1 / n`.

* `BoxIntegral.unitPartition.admissibleIndex`: For `B : BoxIntegral.Box`, the set of indices of
  `unitPartition.box` that are subsets of `B`. This is a finite set.

* `BoxIntegral.unitPartition.prepartition_isPartition`: For `B : BoxIntegral.Box`, if `B`
  has integral vertices, then the prepartition of `unitPartition.box` admissible for `B` is a
  partition of `B`.

* `tendsto_tsum_div_pow_atTop_integral`: let `s` be a bounded, measurable set of `ι → ℝ`
  whose frontier has zero volume and let `F` be a continuous function. Then the limit as `n → ∞`
  of `∑ F x / n ^ card ι`, where the sum is over the points in `s ∩ n⁻¹ • (ι → ℤ)`, tends to the
  integral of `F` over `s`.

* `tendsto_card_div_pow_atTop_volume`: let `s` be a bounded, measurable set of `ι → ℝ` whose
  frontier has zero volume. Then the limit as `n → ∞` of `card (s ∩ n⁻¹ • (ι → ℤ)) / n ^ card ι`
  tends to the volume of `s`.

* `tendsto_card_div_pow_atTop_volume'`: a version of `tendsto_card_div_pow_atTop_volume` where we
  assume in addition that `x • s ⊆ y • s` whenever `0 < x ≤ y`. Then we get the same limit
  `card (s ∩ x⁻¹ • (ι → ℤ)) / x ^ card ι → volume s` but the limit is over a real variable `x`.

-/

noncomputable section

variable {ι : Type*}

open scoped Topology

section hasIntegralVertices

open Bornology

def BoxIntegral.hasIntegralVertices (B : Box ι) : Prop :=
  ∃ l u : ι → ℤ, (∀ i, B.lower i = l i) ∧ (∀ i, B.upper i = u i)

theorem BoxIntegral.le_hasIntegralVertices_of_isBounded [Finite ι] {s : Set (ι → ℝ)}
    (h : IsBounded s) :
    ∃ B : BoxIntegral.Box ι, hasIntegralVertices B ∧ s ≤ B := by
  have := Fintype.ofFinite ι
  obtain ⟨R, hR₁, hR₂⟩ := IsBounded.subset_ball_lt h 0 0
  let C : ℕ := ⌈R⌉₊
  have hC := Nat.ceil_pos.mpr hR₁
  let I : Box ι := Box.mk (fun _ ↦ -C) (fun _ ↦ C)
    (fun _ ↦ by simp [C, neg_lt_self_iff, Nat.cast_pos, hC])
  refine ⟨I, ⟨fun _ ↦ - C, fun _ ↦ C, fun i ↦ (Int.cast_neg_natCast C).symm, fun _ ↦ rfl⟩,
    le_trans hR₂ ?_⟩
  suffices Metric.ball (0 : ι → ℝ) C ≤ I from
    le_trans (Metric.ball_subset_ball (Nat.le_ceil R)) this
  intro x hx
  simp_rw [C, mem_ball_zero_iff, pi_norm_lt_iff (Nat.cast_pos.mpr hC),
    Real.norm_eq_abs, abs_lt] at hx
  exact fun i ↦ ⟨(hx i).1, le_of_lt (hx i).2⟩

end hasIntegralVertices

namespace BoxIntegral.unitPartition

open Bornology MeasureTheory Fintype BoxIntegral

variable (n : ℕ)

-- DISSOLVED: box
