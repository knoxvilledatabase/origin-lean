/-
Extracted from Topology/Closure.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Interior, closure and frontier of a set

This file provides lemmas relating to the functions `interior`, `closure` and `frontier` of a set
endowed with a topology.

## Notation

* `𝓝 x`: the filter `nhds x` of neighborhoods of a point `x`;
* `𝓟 s`: the principal filter of a set `s`;
* `𝓝[s] x`: the filter `nhdsWithin x s` of neighborhoods of a point `x` within a set `s`;
* `𝓝[≠] x`: the filter `nhdsWithin x {x}ᶜ` of punctured neighborhoods of `x`.

## Tags

interior, closure, frontier
-/

open Set

universe u v

variable {X : Type u} [TopologicalSpace X] {ι : Sort v} {x : X} {s s₁ s₂ t : Set X}

section Interior

theorem mem_interior : x ∈ interior s ↔ ∃ t ⊆ s, IsOpen t ∧ x ∈ t := by
  simp only [interior, mem_sUnion, mem_setOf_eq, and_assoc, and_left_comm]
