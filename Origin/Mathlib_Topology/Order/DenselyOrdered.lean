/-
Extracted from Topology/Order/DenselyOrdered.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Order topology on a densely ordered set
-/

open Set Filter TopologicalSpace Topology Function

open OrderDual (toDual ofDual)

variable {α β : Type*}

section DenselyOrdered

variable [TopologicalSpace α] [LinearOrder α] [OrderTopology α] [DenselyOrdered α] {a b : α}
  {s : Set α}

theorem closure_Ioi' {a : α} (h : (Ioi a).Nonempty) : closure (Ioi a) = Ici a := by
  apply Subset.antisymm
  · exact closure_minimal Ioi_subset_Ici_self isClosed_Ici
  · rw [← diff_subset_closure_iff, Ici_diff_Ioi_same, singleton_subset_iff]
    exact isGLB_Ioi.mem_closure h
