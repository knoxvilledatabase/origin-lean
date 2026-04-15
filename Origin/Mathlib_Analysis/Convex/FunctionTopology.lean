/-
Extracted from Analysis/Convex/FunctionTopology.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Topological properties of the set of convex/concave functions

We prove the following facts:

* `isClosed_setOf_convexOn` : the set of convex functions on a set is closed
* `isClosed_setOf_concaveOn` : the set of concave functions on a set is closed
-/

open scoped Topology

open Set

variable {𝕜 α β : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [PartialOrder β]
    [TopologicalSpace β] [OrderClosedTopology β]
    [AddCommMonoid α] [AddCommMonoid β]
    [SMul 𝕜 α] [SMul 𝕜 β]
    [ContinuousConstSMul 𝕜 β] [ContinuousAdd β]

public theorem isClosed_setOf_convexOn {s : Set α} :
    IsClosed {f : α → β | ConvexOn 𝕜 s f} := by
  simp only [ConvexOn, setOf_and, setOf_forall]
  refine IsClosed.inter isClosed_const ?_
  exact isClosed_iInter fun x => isClosed_iInter fun hx => isClosed_iInter fun y =>
      isClosed_iInter fun hy => isClosed_iInter fun a => isClosed_iInter fun b =>
      isClosed_iInter fun ha => isClosed_iInter fun hb => isClosed_iInter fun hab =>
      isClosed_le (by fun_prop) (by fun_prop)

public theorem isClosed_setOf_concaveOn {s : Set α} :
    IsClosed {f : α → β | ConcaveOn 𝕜 s f} :=
  isClosed_setOf_convexOn (α := α) (β := βᵒᵈ)
