/-
Extracted from Analysis/Normed/Affine/Isometry.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Affine isometries

In this file we define `AffineIsometry 𝕜 P P₂` to be an affine isometric embedding of normed
add-torsors `P` into `P₂` over normed `𝕜`-spaces and `AffineIsometryEquiv` to be an affine
isometric equivalence between `P` and `P₂`.

We also prove basic lemmas and provide convenience constructors.  The choice of these lemmas and
constructors is closely modelled on those for the `LinearIsometry` and `AffineMap` theories.

Since many elementary properties don't require `‖x‖ = 0 → x = 0` we initially set up the theory for
`SeminormedAddCommGroup` and specialize to `NormedAddCommGroup` only when needed.

## Notation

We introduce the notation `P →ᵃⁱ[𝕜] P₂` for `AffineIsometry 𝕜 P P₂`, and `P ≃ᵃⁱ[𝕜] P₂` for
`AffineIsometryEquiv 𝕜 P P₂`.  In contrast with the notation `→ₗᵢ` for linear isometries, `≃ᵢ`
for isometric equivalences, etc., the "i" here is a superscript.  This is for aesthetic reasons to
match the superscript "a" (note that in mathlib `→ᵃ` is an affine map, since `→ₐ` has been taken by
algebra-homomorphisms.)

-/

open Function Set Metric

variable (𝕜 : Type*) {V V₁ V₁' V₂ V₃ V₄ : Type*} {P₁ P₁' : Type*} (P P₂ : Type*) {P₃ P₄ : Type*}
  [NormedField 𝕜]
  [SeminormedAddCommGroup V] [NormedSpace 𝕜 V] [PseudoMetricSpace P] [NormedAddTorsor V P]
  [SeminormedAddCommGroup V₁] [NormedSpace 𝕜 V₁] [PseudoMetricSpace P₁] [NormedAddTorsor V₁ P₁]
  [SeminormedAddCommGroup V₁'] [NormedSpace 𝕜 V₁'] [MetricSpace P₁'] [NormedAddTorsor V₁' P₁']
  [SeminormedAddCommGroup V₂] [NormedSpace 𝕜 V₂] [PseudoMetricSpace P₂] [NormedAddTorsor V₂ P₂]
  [SeminormedAddCommGroup V₃] [NormedSpace 𝕜 V₃] [PseudoMetricSpace P₃] [NormedAddTorsor V₃ P₃]
  [SeminormedAddCommGroup V₄] [NormedSpace 𝕜 V₄] [PseudoMetricSpace P₄] [NormedAddTorsor V₄ P₄]

structure AffineIsometry extends P →ᵃ[𝕜] P₂ where
  norm_map : ∀ x : V, ‖linear x‖ = ‖x‖

variable {𝕜 P P₂}
