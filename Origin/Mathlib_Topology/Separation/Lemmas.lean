/-
Extracted from Topology/Separation/Lemmas.lean
Genuine: 2 of 4 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Further separation lemmas
-/

variable {X : Type*}

namespace CompletelyRegularSpace

variable [TopologicalSpace X] [T35Space X]

theorem totallySeparatedSpace_of_cardinalMk_lt_continuum (h : Cardinal.mk X < Cardinal.continuum) :
    TotallySeparatedSpace X :=
  totallySeparatedSpace_of_t0_of_basis_clopen <|
    CompletelyRegularSpace.isTopologicalBasis_clopens_of_cardinalMk_lt_continuum h

-- INSTANCE (free from Core): [Countable

end CompletelyRegularSpace

theorem Set.Countable.isTotallyDisconnected [MetricSpace X] {s : Set X} (hs : s.Countable) :
    IsTotallyDisconnected s := by
  rw [← totallyDisconnectedSpace_subtype_iff]
  have : Countable s := hs
  infer_instance
