/-
Extracted from Topology/Compactness/Lindelof.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Lindelöf sets and Lindelöf spaces

## Main definitions

We define the following properties for sets in a topological space:

* `IsLindelof s`: Two definitions are possible here. The more standard definition is that
  every open cover that contains `s` contains a countable subcover. We choose for the equivalent
  definition where we require that every nontrivial filter on `s` with the countable intersection
  property has a cluster point. Equivalence is established in `isLindelof_iff_countable_subcover`.
* `LindelofSpace X`: `X` is Lindelöf if it is Lindelöf as a set.
* `NonLindelofSpace`: a space that is not a Lindelöf space, e.g. the Long Line.

## Main results

* `isLindelof_iff_countable_subcover`: A set is Lindelöf iff every open cover has a
  countable subcover.

## Implementation details

* This API is mainly based on the API for IsCompact and follows notation and style as much
  as possible.
-/

open Set Filter Topology TopologicalSpace

universe u v

variable {X : Type u} {Y : Type v} {ι : Type*}

variable [TopologicalSpace X] [TopologicalSpace Y] {s t : Set X}

section Lindelof

def IsLindelof (s : Set X) :=
  ∀ ⦃f⦄ [NeBot f] [CountableInterFilter f], f ≤ 𝓟 s → ∃ x ∈ s, ClusterPt x f

theorem IsLindelof.compl_mem_sets (hs : IsLindelof s) {f : Filter X} [CountableInterFilter f]
    (hf : ∀ x ∈ s, sᶜ ∈ 𝓝 x ⊓ f) : sᶜ ∈ f := by
  contrapose! hf
  simp only [notMem_iff_inf_principal_compl, compl_compl, inf_assoc] at hf ⊢
  exact hs inf_le_right

theorem IsLindelof.compl_mem_sets_of_nhdsWithin (hs : IsLindelof s) {f : Filter X}
    [CountableInterFilter f] (hf : ∀ x ∈ s, ∃ t ∈ 𝓝[s] x, tᶜ ∈ f) : sᶜ ∈ f := by
  refine hs.compl_mem_sets fun x hx ↦ ?_
  rw [← disjoint_principal_right, disjoint_right_comm, (basis_sets _).disjoint_iff_left]
  exact hf x hx
