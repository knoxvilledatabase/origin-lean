/-
Extracted from Analysis/InnerProductSpace/Calculus.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Calculus in inner product spaces

In this file we prove that the inner product and square of the norm in an inner space are
infinitely `ℝ`-smooth. In order to state these results, we need a `NormedSpace ℝ E`
instance. Though we can deduce this structure from `InnerProductSpace 𝕜 E`, this instance may be
not definitionally equal to some other “natural” instance. So, we assume `[NormedSpace ℝ E]`.

We also prove that functions to a `EuclideanSpace` are (higher) differentiable if and only if
their components are. This follows from the corresponding fact for finite product of normed spaces,
and from the equivalence of norms in finite dimensions.

## TODO

The last part of the file should be generalized to `PiLp`.
-/

noncomputable section

open RCLike Real Filter

section DerivInner

variable {𝕜 E F : Type*} [RCLike 𝕜]

variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

variable (𝕜) [NormedSpace ℝ E]

def fderivInnerCLM (p : E × E) : E × E →L[ℝ] 𝕜 :=
  isBoundedBilinearMap_inner.deriv p
