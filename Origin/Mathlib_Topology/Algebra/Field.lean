/-
Extracted from Topology/Algebra/Field.lean
Genuine: 6 of 8 | Dissolved: 2 | Infrastructure: 0
-/
import Origin.Core

/-!
# Topological fields

A topological division ring is a topological ring whose inversion function is continuous at every
non-zero element.

-/

variable {K : Type*} [DivisionRing K] [TopologicalSpace K]

-- DISSOLVED: Filter.tendsto_cocompact_mul_left₀

-- DISSOLVED: Filter.tendsto_cocompact_mul_right₀

theorem DivisionRing.finite_of_compactSpace_of_t2Space {K} [DivisionRing K] [TopologicalSpace K]
    [IsTopologicalRing K] [CompactSpace K] [T2Space K] : Finite K := by
  suffices DiscreteTopology K by
    exact finite_of_compact_of_discrete
  rw [discreteTopology_iff_isOpen_singleton_zero]
  exact GroupWithZero.isOpen_singleton_zero

variable (K)

class IsTopologicalDivisionRing : Prop extends IsTopologicalRing K, ContinuousInv₀ K

section Subfield

variable {α : Type*} [Field α] [TopologicalSpace α] [IsTopologicalDivisionRing α]

def Subfield.topologicalClosure (K : Subfield α) : Subfield α :=
  { K.toSubring.topologicalClosure with
    carrier := _root_.closure (K : Set α)
    inv_mem' := fun x hx => by
      rcases eq_or_ne x 0 with (rfl | h)
      · rwa [inv_zero]
      · rw [← inv_coe_set, ← Set.image_inv_eq_inv]
        exact mem_closure_image (continuousAt_inv₀ h) hx }

theorem Subfield.le_topologicalClosure (s : Subfield α) : s ≤ s.topologicalClosure :=
  _root_.subset_closure

theorem Subfield.isClosed_topologicalClosure (s : Subfield α) :
    IsClosed (s.topologicalClosure : Set α) :=
  isClosed_closure

theorem Subfield.topologicalClosure_minimal (s : Subfield α) {t : Subfield α} (h : s ≤ t)
    (ht : IsClosed (t : Set α)) : s.topologicalClosure ≤ t :=
  closure_minimal h ht

end Subfield

section Units
