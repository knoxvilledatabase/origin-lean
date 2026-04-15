/-
Extracted from Topology/Algebra/Star/Unitary.lean
Genuine: 1 of 4 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-! # Topological properties of the unitary (sub)group

* In a topological star monoid `R`, `unitary R` is a topological group
* In a topological star monoid `R` which is T1, `unitary R` is closed as a subset of `R`.
-/

variable {R : Type*} [Monoid R] [StarMul R] [TopologicalSpace R]

-- INSTANCE (free from Core): [ContinuousStar

-- INSTANCE (free from Core): [ContinuousStar

-- INSTANCE (free from Core): [ContinuousMul

lemma isClosed_unitary [T1Space R] [ContinuousStar R] [ContinuousMul R] :
    IsClosed (unitary R : Set R) := by
  let f (u : R) : R × R := (star u * u, u * star u)
  have hf : f ⁻¹' {(1, 1)} = unitary R := by ext u; simp [f, Unitary.mem_iff]
  rw [← hf]
  exact isClosed_singleton.preimage (by fun_prop)
