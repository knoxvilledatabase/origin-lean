/-
Extracted from Analysis/Convex/Contractible.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# A convex set is contractible

In this file we prove that a (star) convex set in a real topological vector space is a contractible
topological space.
-/

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [ContinuousAdd E]
  [ContinuousSMul ℝ E] {s : Set E} {x : E}

protected theorem StarConvex.contractibleSpace (h : StarConvex ℝ x s) (hne : s.Nonempty) :
    ContractibleSpace s := by
  refine
    (contractible_iff_id_nullhomotopic s).2 ⟨⟨x, h.mem hne⟩,
      ⟨⟨⟨fun p ↦ ⟨p.1.1 • x + (1 - p.1.1) • (p.2 : E), ?_⟩, ?_⟩, fun x ↦ by simp, fun x ↦ by simp⟩⟩⟩
  · exact h p.2.2 p.1.2.1 (sub_nonneg.2 p.1.2.2) (add_sub_cancel _ _)
  · exact Continuous.subtype_mk (by fun_prop) _

protected theorem Convex.contractibleSpace (hs : Convex ℝ s) (hne : s.Nonempty) :
    ContractibleSpace s :=
  let ⟨_, hx⟩ := hne
  (hs.starConvex hx).contractibleSpace hne

-- INSTANCE (free from Core): (priority
