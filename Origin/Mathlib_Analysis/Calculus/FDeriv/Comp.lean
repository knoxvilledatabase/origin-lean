/-
Extracted from Analysis/Calculus/FDeriv/Comp.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The derivative of a composition (chain rule)

For detailed documentation of the Fréchet derivative,
see the module docstring of `Mathlib/Analysis/Calculus/FDeriv/Basic.lean`.

This file contains the usual formulas (and existence assertions) for the derivative of
composition of functions (the chain rule).
-/

open Filter Asymptotics ContinuousLinearMap Set Metric Topology NNReal ENNReal

noncomputable section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

variable {G' : Type*} [NormedAddCommGroup G'] [NormedSpace 𝕜 G']

variable {f g : E → F} {f' g' : E →L[𝕜] F} {x : E} {s : Set E} {L : Filter (E × E)}

section Composition

/-!
### Derivative of the composition of two functions

For composition lemmas, we put `x` explicit to help the elaborator, as otherwise Lean tends to
get confused since there are too many possibilities for composition. -/

variable (x)

theorem HasFDerivAtFilter.comp {g : F → G} {g' : F →L[𝕜] G} {L' : Filter (F × F)}
    (hg : HasFDerivAtFilter g g' L') (hf : HasFDerivAtFilter f f' L)
    (hL : Tendsto (Prod.map f f) L L') :
    HasFDerivAtFilter (g ∘ f) (g' ∘L f') L := by
  -- This proof can be golfed a lot. However, it should be left this way for readability.
  refine .of_isLittleOTVS <| calc
    (fun p ↦ (g ∘ f) p.1 - (g ∘ f) p.2 - (g' ∘L f') (p.1 - p.2))
      = fun p ↦ (g (f p.1) - g (f p.2) - g' (f p.1 - f p.2)) +
          g' (f p.1 - f p.2 - f' (p.1 - p.2)) := by
      ext; simp
    _ =o[𝕜; L] (fun p ↦ p.1 - p.2) := .add ?Hg ?Hf
  case Hg => calc (fun p ↦ g (f p.1) - g (f p.2) - g' (f p.1 - f p.2))
    _ =o[𝕜; L] (fun p ↦ f p.1 - f p.2) :=
      hg.isLittleOTVS.comp_tendsto hL
    _ =O[𝕜; L] (fun p ↦ p.1 - p.2) := hf.isBigOTVS_sub
  case Hf => calc (fun p ↦ g' (f p.1 - f p.2 - f' (p.1 - p.2)))
    _ =O[𝕜; L] (fun p ↦ f p.1 - f p.2 - f' (p.1 - p.2)) := g'.isBigOTVS_comp
    _ =o[𝕜; L] (fun p ↦ p.1 - p.2) := hf.isLittleOTVS
