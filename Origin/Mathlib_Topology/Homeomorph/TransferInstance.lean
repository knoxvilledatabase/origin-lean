/-
Extracted from Topology/Homeomorph/TransferInstance.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Transfer topological structure across `Equiv`s

We show how to transport a topological space structure across an `Equiv` and prove that this
make the equivalence a homeomorphism between the original space and the transported topology.

-/

variable {R α β : Type*}

namespace Equiv

protected abbrev topologicalSpace [TopologicalSpace β] (e : α ≃ β) :
    TopologicalSpace α :=
  .induced e ‹_›

def homeomorph [TopologicalSpace β] (e : α ≃ β) :
    letI := e.topologicalSpace
    α ≃ₜ β :=
  letI := e.topologicalSpace
  { e with
    continuous_toFun := continuous_induced_dom
    continuous_invFun := by
      simp only [Equiv.invFun_as_coe]
      convert continuous_coinduced_rng
      rw [e.coinduced_symm] }

end Equiv
