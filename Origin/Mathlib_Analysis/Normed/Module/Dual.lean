/-
Extracted from Analysis/Normed/Module/Dual.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Polar sets in the strong dual of a normed space

In this file we study polar sets in the strong dual `StrongDual` of a normed space.

## Main definitions

* `polar 𝕜 s` is the subset of `StrongDual 𝕜 E` consisting of those functionals `x'` for which
  `‖x' z‖ ≤ 1` for every `z ∈ s`.

## References

* [Conway, John B., A course in functional analysis][conway1990]

## Tags

strong dual, polar
-/

noncomputable section

open Topology Bornology

namespace NormedSpace

section PolarSets

open Metric Set StrongDual

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem isClosed_polar (s : Set E) : IsClosed (StrongDual.polar 𝕜 s) := by
  dsimp only [StrongDual.polar]
  simp only [LinearMap.polar_eq_iInter, LinearMap.flip_apply]
  refine isClosed_biInter fun z _ => ?_
  exact isClosed_Iic.preimage (ContinuousLinearMap.apply 𝕜 𝕜 z).continuous.norm
