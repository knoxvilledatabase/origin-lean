/-
Extracted from Topology/Algebra/Valued/ValuativeRel.lean
Genuine: 1 of 4 | Dissolved: 1 | Infrastructure: 2
-/
import Origin.Core

/-!

# Valuative Relations as Valued

In this temporary file, we provide a helper instance
for `Valued R Γ` derived from a `ValuativeRel R`,
so that downstream files can refer to `ValuativeRel R`,
to facilitate a refactor.

-/

namespace IsValuativeTopology

/-! ### Alternate constructors -/

variable {R : Type*} [CommRing R] [ValuativeRel R] [TopologicalSpace R]

open ValuativeRel TopologicalSpace Filter Topology Set

local notation "v" => valuation R

-- DISSOLVED: of_zero

end

variable {R : Type*} [CommRing R] [ValuativeRel R] [TopologicalSpace R] [IsValuativeTopology R]

open ValuativeRel TopologicalSpace Filter Topology Set

local notation "v" => valuation R

-- INSTANCE (free from Core): (priority

open WithZeroTopology in

lemma continuous_valuation : Continuous v := by
  simp only [continuous_iff_continuousAt, ContinuousAt]
  rintro x
  by_cases hx : v x = 0
  · simpa [hx, ((valuation R).hasBasis_nhds _).tendsto_iff WithZeroTopology.hasBasis_nhds_zero]
      using fun i hi ↦ ⟨(Units.mk0 i hi).mapEquiv (ValueGroupWithZero.orderMonoidIso (valuation R)),
        fun y ↦ by simp [Valuation.map_sub_of_right_eq_zero _ hx]⟩
  · simpa [((valuation R).hasBasis_nhds _).tendsto_iff (hasBasis_nhds_of_ne_zero hx)]
      using ⟨(Units.mk0 (v x) hx).mapEquiv (ValueGroupWithZero.orderMonoidIso (valuation R)),
        fun _ ↦ by simpa [← (valuation R).restrict_def] using Valuation.map_eq_of_sub_lt _⟩

end IsValuativeTopology

namespace ValuativeRel
