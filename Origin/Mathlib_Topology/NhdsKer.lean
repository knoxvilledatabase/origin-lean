/-
Extracted from Topology/NhdsKer.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Neighborhoods kernel of a set

In `Mathlib/Topology/Defs/Filter.lean`, `nhdsKer s` is defined to be the intersection of all
neighborhoods of `s`.
Note that this construction has no standard name in the literature.

In this file we prove basic properties of this operation.
-/

open Set Filter

open scoped Topology

variable {ι : Sort*} {X : Type*} [TopologicalSpace X] {s t : Set X} {x y : X}

lemma nhdsKer_singleton_eq_ker_nhds (x : X) : nhdsKer {x} = (𝓝 x).ker := by simp [nhdsKer]
