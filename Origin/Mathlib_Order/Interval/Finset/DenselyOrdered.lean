/-
Extracted from Order/Interval/Finset/DenselyOrdered.lean
Genuine: 2 of 4 | Dissolved: 2 | Infrastructure: 0
-/
import Origin.Core

/-!
# Linear locally finite orders are densely ordered iff they are trivial

## Main results
* `LocallyFiniteOrder.denselyOrdered_iff_subsingleton`:
  A linear locally finite order is densely ordered if and only if it is a subsingleton.

-/

variable {X : Type*} [LinearOrder X] [LocallyFiniteOrder X]

lemma LocallyFiniteOrder.denselyOrdered_iff_subsingleton :
    DenselyOrdered X ↔ Subsingleton X := by
  refine ⟨fun H ↦ ?_, fun h ↦ h.instDenselyOrdered⟩
  rw [← not_nontrivial_iff_subsingleton, nontrivial_iff_lt]
  rintro ⟨a, b, hab⟩
  exact not_lt_of_denselyOrdered_of_locallyFinite a b hab

lemma denselyOrdered_set_iff_subsingleton {s : Set X} :
    DenselyOrdered s ↔ s.Subsingleton := by
  classical
  simp [LocallyFiniteOrder.denselyOrdered_iff_subsingleton]

-- DISSOLVED: WithBot.denselyOrdered_set_iff_subsingleton

-- DISSOLVED: WithTop.denselyOrdered_set_iff_subsingleton
