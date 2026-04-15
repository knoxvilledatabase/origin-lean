/-
Extracted from Analysis/Calculus/FDeriv/Linear.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The derivative of bounded linear maps

For detailed documentation of the Fréchet derivative,
see the module docstring of `Mathlib/Analysis/Calculus/FDeriv/Basic.lean`.

This file contains the usual formulas (and existence assertions) for the derivative of
bounded linear maps.
-/

open Asymptotics

namespace ContinuousLinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

variable {E : Type*} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]

variable {F : Type*} [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]

variable (f : E →L[𝕜] F)

variable {x : E}

variable {s : Set E}

variable {L : Filter (E × E)}

/-!
### Bundled continuous linear maps

There are currently two variants of these in mathlib, the bundled version
(named `ContinuousLinearMap`, and denoted `E →L[𝕜] F`, works for topological vector spaces),
and the unbundled version (with a predicate `IsBoundedLinearMap`, requires normed spaces).
This section deals with the first form, see below for the unbundled version
-/

protected theorem hasFDerivAtFilter : HasFDerivAtFilter f f L :=
  .of_isLittleOTVS <| (IsLittleOTVS.zero _ _).congr_left fun x => by
    simp only [f.map_sub, sub_self, Pi.zero_apply]
