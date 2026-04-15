/-
Extracted from Analysis/InnerProductSpace/Rayleigh.lean
Genuine: 2 of 3 | Dissolved: 1 | Infrastructure: 0
-/
import Origin.Core

/-!
# The Rayleigh quotient

The Rayleigh quotient of a self-adjoint operator `T` on an inner product space `E` is the function
`fun x ↦ ⟪T x, x⟫ / ‖x‖ ^ 2`.

The main results of this file are `IsSelfAdjoint.hasEigenvector_of_isMaxOn` and
`IsSelfAdjoint.hasEigenvector_of_isMinOn`, which state that if `E` is complete, and if the
Rayleigh quotient attains its global maximum/minimum over some sphere at the point `x₀`, then `x₀`
is an eigenvector of `T`, and the `iSup`/`iInf` of `fun x ↦ ⟪T x, x⟫ / ‖x‖ ^ 2` is the corresponding
eigenvalue.

The corollaries `LinearMap.IsSymmetric.hasEigenvalue_iSup_of_finiteDimensional` and
`LinearMap.IsSymmetric.hasEigenvalue_iSup_of_finiteDimensional` state that if `E` is
finite-dimensional and nontrivial, then `T` has some (nonzero) eigenvectors with eigenvalue the
`iSup`/`iInf` of `fun x ↦ ⟪T x, x⟫ / ‖x‖ ^ 2`.

## TODO

A slightly more elaborate corollary is that if `E` is complete and `T` is a compact operator, then
`T` has some (nonzero) eigenvector with eigenvalue either `⨆ x, ⟪T x, x⟫ / ‖x‖ ^ 2` or
`⨅ x, ⟪T x, x⟫ / ‖x‖ ^ 2` (not necessarily both).

-/

variable {𝕜 : Type*} [RCLike 𝕜]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

open scoped NNReal

open Module.End Metric RCLike InnerProductSpace

namespace ContinuousLinearMap

variable (T : E →L[𝕜] E)

noncomputable abbrev rayleighQuotient (x : E) := T.reApplyInnerSelf x / ‖(x : E)‖ ^ 2

-- DISSOLVED: rayleigh_smul

theorem rayleighQuotient_add (S : E →L[𝕜] E) {x : E} :
    (T + S).rayleighQuotient x = T.rayleighQuotient x + S.rayleighQuotient x := by
  simp [rayleighQuotient, reApplyInnerSelf_apply, inner_add_left, add_div]
