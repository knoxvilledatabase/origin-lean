/-
Extracted from Topology/Perfect.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Perfect Sets

In this file we define perfect subsets of a topological space, and prove some basic properties,
including a version of the Cantor-Bendixson Theorem.

## Main Definitions

* `Preperfect C`: A set `C` is preperfect if every point of `C` is an accumulation point
  of `C`. Equivalently, if it has no isolated points in the induced topology.
  This property is also called dense-in-itself.
* `Perfect C`: A set `C` is perfect, meaning it is closed and every point of it
  is an accumulation point of itself.
* `PerfectSpace X`: A topological space `X` is perfect if its universe is a perfect set.

## Main Statements

* `preperfect_iff_perfect_closure`: In a T1 space, a set is preperfect iff its closure is perfect.
* `Perfect.splitting`: A perfect nonempty set contains two disjoint perfect nonempty subsets.
  The main inductive step in the construction of an embedding from the Cantor space to a
  perfect nonempty complete metric space.
* `exists_countable_union_perfect_of_isClosed`: One version of the **Cantor-Bendixson Theorem**:
  A closed set in a second countable space can be written as the union of a countable set and a
  perfect set.

## Implementation Notes

We do not require perfect sets to be nonempty.

## See also

`Mathlib/Topology/MetricSpace/Perfect.lean`, for properties of perfect sets in metric spaces,
namely Polish spaces.

## References

* [kechris1995] (Chapters 6-7)

## Tags

accumulation point, perfect set, dense-in-itself, cantor-bendixson.

-/

open Topology Filter Set TopologicalSpace

section Basic

variable {α : Type*} [TopologicalSpace α] {C : Set α}

theorem AccPt.nhds_inter {x : α} {U : Set α} (h_acc : AccPt x (𝓟 C)) (hU : U ∈ 𝓝 x) :
    AccPt x (𝓟 (U ∩ C)) := by
  have : 𝓝[≠] x ≤ 𝓟 U := by
    rw [le_principal_iff]
    exact mem_nhdsWithin_of_mem_nhds hU
  rw [AccPt, ← inf_principal, ← inf_assoc, inf_of_le_left this]
  exact h_acc

def Preperfect (C : Set α) : Prop :=
  ∀ x ∈ C, AccPt x (𝓟 C)
