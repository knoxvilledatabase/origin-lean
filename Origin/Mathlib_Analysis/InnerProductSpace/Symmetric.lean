/-
Extracted from Analysis/InnerProductSpace/Symmetric.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Symmetric linear maps in an inner product space

This file defines and proves basic theorems about symmetric **not necessarily bounded** operators
on an inner product space, i.e linear maps `T : E → E` such that `∀ x y, ⟪T x, y⟫ = ⟪x, T y⟫`.

In comparison to `IsSelfAdjoint`, this definition works for non-continuous linear maps, and
doesn't rely on the definition of the adjoint, which allows it to be stated in non-complete space.

## Main definitions

* `LinearMap.IsSymmetric`: a (not necessarily bounded) operator on an inner product space is
  symmetric, if for all `x`, `y`, we have `⟪T x, y⟫ = ⟪x, T y⟫`

## Main statements

* `IsSymmetric.continuous`: if a symmetric operator is defined on a complete space, then
  it is automatically continuous.

## Tags

self-adjoint, symmetric
-/

open RCLike

open ComplexConjugate

section Seminormed

variable {𝕜 E : Type*} [RCLike 𝕜]

variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

namespace LinearMap

/-! ### Symmetric operators -/

def IsSymmetric (T : E →ₗ[𝕜] E) : Prop :=
  ∀ x y, ⟪T x, y⟫ = ⟪x, T y⟫

section Real

theorem isSymmetric_iff_sesqForm (T : E →ₗ[𝕜] E) :
    T.IsSymmetric ↔ LinearMap.IsSelfAdjoint (R := 𝕜) (M := E) (LinearMap.flip (innerₛₗ 𝕜)) T :=
  ⟨fun h x y => (h y x).symm, fun h x y => (h y x).symm⟩

end Real

theorem IsSymmetric.conj_inner_sym {T : E →ₗ[𝕜] E} (hT : IsSymmetric T) (x y : E) :
    conj ⟪T x, y⟫ = ⟪T y, x⟫ := by rw [hT x y, inner_conj_symm]
