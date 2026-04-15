/-
Extracted from MeasureTheory/Measure/Support.lean
Genuine: 7 of 9 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Support of a Measure

This file develops the theory of the **support** of a measure `μ` on a
topological measurable space. The support is defined as the set of points whose every open
neighborhood has positive measure. We give equivalent characterizations, prove basic
measure-theoretic properties, and study interactions with sums, restrictions, and
absolute continuity. Under various Lindelöf conditions, the support is conull,
and various descriptions of the complement of the support are provided.

## Main definitions

* `Measure.support` : the support of a measure `μ`, defined as
  `{x | ∃ᶠ u in (𝓝 x).smallSets, 0 < μ u}` — equivalently, every neighborhood of `x`
  has positive `μ`-measure.

## Main results

* `compl_support_eq_sUnion` and `support_eq_sInter` : the complement of the support is the
  union of open measure-zero sets, and the support is the intersection of closed sets whose
  complements have measure zero.
* `isClosed_support` : the support is a closed set.
* `support_mem_ae_of_isLindelof` and `support_mem_ae` : under Lindelöf (or hereditarily
  Lindelöf) hypotheses, the support is conull.

## Tags

measure, support, Lindelöf
-/

section Support

namespace MeasureTheory

namespace Measure

open scoped Topology

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]

protected def support (μ : Measure X) : Set X := {x : X | ∃ᶠ u in (𝓝 x).smallSets, 0 < μ u}

variable {μ : Measure X}

theorem _root_.Filter.HasBasis.mem_measureSupport {ι : Sort*} {p : ι → Prop}
    {s : ι → Set X} {x : X} (hl : (𝓝 x).HasBasis p s) :
    x ∈ μ.support ↔ ∀ (i : ι), p i → 0 < μ (s i) :=
  hl.frequently_smallSets pos_mono

lemma mem_support_iff_forall (x : X) : x ∈ μ.support ↔ ∀ U ∈ 𝓝 x, 0 < μ U :=
  (𝓝 x).basis_sets.mem_measureSupport

lemma support_eq_univ [μ.IsOpenPosMeasure] : μ.support = Set.univ := by
  simpa [Set.eq_univ_iff_forall, mem_support_iff_forall] using fun _ _ ↦ μ.measure_pos_of_mem_nhds

lemma AbsolutelyContinuous.support_mono {μ ν : Measure X} (hμν : μ ≪ ν) :
    μ.support ⊆ ν.support :=
  fun _ hx ↦ hx.mp <| .of_forall hμν.pos_mono

lemma notMem_support_iff {x : X} : x ∉ μ.support ↔ ∀ᶠ u in (𝓝 x).smallSets, μ u = 0 := by
  simp [mem_support_iff]

theorem _root_.Filter.HasBasis.notMem_measureSupport {ι : Sort*} {p : ι → Prop}
    {s : ι → Set X} {x : X} (hl : (𝓝 x).HasBasis p s) :
    x ∉ μ.support ↔ ∃ i, p i ∧ μ (s i) = 0 := by
  simp [hl.mem_measureSupport]
