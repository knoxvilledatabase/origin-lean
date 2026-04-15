/-
Extracted from Analysis/Calculus/FDeriv/Prod.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Derivative of the Cartesian product of functions

For detailed documentation of the Fréchet derivative,
see the module docstring of `Mathlib/Analysis/Calculus/FDeriv/Basic.lean`.

This file contains the usual formulas (and existence assertions) for the derivative of
Cartesian products of functions, and functions into Pi-types.
-/

open Filter Asymptotics ContinuousLinearMap Set Metric Topology NNReal ENNReal

noncomputable section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

variable {G' : Type*} [NormedAddCommGroup G'] [NormedSpace 𝕜 G']

variable {f f₀ f₁ g : E → F}

variable {f' f₀' f₁' g' : E →L[𝕜] F}

variable (e : E →L[𝕜] F)

variable {x : E}

variable {s t : Set E}

variable {L : Filter (E × E)}

section CartesianProduct

/-! ### Derivative of the Cartesian product of two functions -/

section Prod

variable {f₂ : E → G} {f₂' : E →L[𝕜] G}

theorem HasFDerivAtFilter.prodMk (hf₁ : HasFDerivAtFilter f₁ f₁' L)
    (hf₂ : HasFDerivAtFilter f₂ f₂' L) :
    HasFDerivAtFilter (fun x => (f₁ x, f₂ x)) (f₁'.prod f₂') L :=
  .of_isLittleO <| hf₁.isLittleO.prod_left hf₂.isLittleO

protected theorem HasStrictFDerivAt.prodMk (hf₁ : HasStrictFDerivAt f₁ f₁' x)
    (hf₂ : HasStrictFDerivAt f₂ f₂' x) :
    HasStrictFDerivAt (fun x => (f₁ x, f₂ x)) (f₁'.prod f₂') x :=
  HasFDerivAtFilter.prodMk hf₁ hf₂
