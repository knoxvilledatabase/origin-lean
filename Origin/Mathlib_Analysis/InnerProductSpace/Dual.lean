/-
Extracted from Analysis/InnerProductSpace/Dual.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The Fréchet-Riesz representation theorem

We consider an inner product space `E` over `𝕜`, which is either `ℝ` or `ℂ`. We define
`toDualMap`, a conjugate-linear isometric embedding of `E` into its dual, which maps an element `x`
of the space to `fun y => ⟪x, y⟫`.

Under the hypothesis of completeness (i.e., for Hilbert spaces), we upgrade this to `toDual`, a
conjugate-linear isometric *equivalence* of `E` onto its dual; that is, we establish the
surjectivity of `toDualMap`.  This is the Fréchet-Riesz representation theorem: every element of the
dual of a Hilbert space `E` has the form `fun u => ⟪x, u⟫` for some `x : E`.

For a bounded sesquilinear form `B : E →L⋆[𝕜] E →L[𝕜] 𝕜`,
we define a map `InnerProductSpace.continuousLinearMapOfBilin B : E →L[𝕜] E`,
given by substituting `E →L[𝕜] 𝕜` with `E` using `toDual`.


## References

* [M. Einsiedler and T. Ward, *Functional Analysis, Spectral Theory, and Applications*]
  [EinsiedlerWard2017]

## Tags

dual, Fréchet-Riesz
-/

noncomputable section

open ComplexConjugate Module

namespace InnerProductSpace

open RCLike ContinuousLinearMap

variable (𝕜 E : Type*)

section Seminormed

variable [RCLike 𝕜] [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

local postfix:90 "†" => starRingEnd _

def toDualMap : E →ₗᵢ⋆[𝕜] StrongDual 𝕜 E :=
  { innerSL 𝕜 with norm_map' := innerSL_apply_norm _ }

variable {E}
