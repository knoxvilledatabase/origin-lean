/-
Extracted from Analysis/Analytic/OfScalars.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Scalar series

This file contains API for analytic functions `∑ cᵢ • xⁱ` defined in terms of scalars
`c₀, c₁, c₂, …`.
## Main definitions / results:
* `FormalMultilinearSeries.ofScalars`: the formal power series `∑ cᵢ • xⁱ`.
* `FormalMultilinearSeries.ofScalarsSum`: the sum of such a power series, if it exists, and zero
  otherwise.
* `FormalMultilinearSeries.ofScalars_radius_eq_(zero/inv/top)_of_tendsto`:
  the ratio test for an analytic function defined in terms of a formal power series `∑ cᵢ • xⁱ`.
* `FormalMultilinearSeries.ofScalars_radius_eq_inv_of_tendsto_ENNReal`:
  the ratio test for an analytic function using `ENNReal` division for all values `ℝ≥0∞`.
-/

namespace FormalMultilinearSeries

section Field

open ContinuousMultilinearMap

variable {𝕜 : Type*} (E : Type*) [Field 𝕜] [Ring E] [Algebra 𝕜 E] [TopologicalSpace E]
  [IsTopologicalRing E] {c : ℕ → 𝕜}

def ofScalars (c : ℕ → 𝕜) : FormalMultilinearSeries 𝕜 E E :=
  fun n ↦ c n • ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 n E
