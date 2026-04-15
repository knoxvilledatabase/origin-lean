/-
Extracted from MeasureTheory/Constructions/SimpleGraph.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Sigma-algebra on simple graphs

In this file, we pull back the sigma-algebra on `V → V → Prop` to a sigma-algebra on
`SimpleGraph V` and prove that common operations are measurable.
-/

open MeasureTheory

open scoped Finset

namespace SimpleGraph

variable {V : Type*}

-- INSTANCE (free from Core): :

lemma measurable_iff_adj {Ω : Type*} {m : MeasurableSpace Ω} {G : Ω → SimpleGraph V} :
    Measurable G ↔ ∀ u v, Measurable fun ω ↦ (G ω).Adj u v := by
  simp [measurable_comap_iff, measurable_pi_iff]
