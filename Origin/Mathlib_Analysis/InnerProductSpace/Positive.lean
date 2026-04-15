/-
Extracted from Analysis/InnerProductSpace/Positive.lean
Genuine: 10 of 10 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Positive operators

In this file we define when an operator in a Hilbert space is positive. We follow Bourbaki's choice
of requiring self adjointness in the definition.

## Main definitions

* `LinearMap.IsPositive` : a linear map is positive if it is symmetric and
  `∀ x, 0 ≤ re ⟪T x, x⟫`.
* `ContinuousLinearMap.IsPositive` : a continuous linear map is positive if it is symmetric and
  `∀ x, 0 ≤ re ⟪T x, x⟫`.

## Main statements

* `ContinuousLinearMap.IsPositive.conj_adjoint` : if `T : E →L[𝕜] E` is positive,
  then for any `S : E →L[𝕜] F`, `S ∘L T ∘L S†` is also positive.
* `ContinuousLinearMap.isPositive_iff_complex` : in a ***complex*** Hilbert space,
  checking that `⟪T x, x⟫` is a nonnegative real number for all `x` suffices to prove that
  `T` is positive.

## References

* [Bourbaki, *Topological Vector Spaces*][bourbaki1987]

## Tags

Positive operator
-/

open InnerProductSpace RCLike LinearMap ContinuousLinearMap

open scoped InnerProduct ComplexConjugate ComplexOrder

variable {𝕜 E F : Type*} [RCLike 𝕜]

variable [NormedAddCommGroup E] [NormedAddCommGroup F]

variable [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

namespace LinearMap

def IsPositive (T : E →ₗ[𝕜] E) : Prop :=
  IsSymmetric T ∧ ∀ x, 0 ≤ re ⟪T x, x⟫

theorem IsPositive.isSymmetric {T : E →ₗ[𝕜] E} (hT : IsPositive T) :
    IsSymmetric T := hT.1

theorem IsPositive.re_inner_nonneg_left {T : E →ₗ[𝕜] E} (hT : IsPositive T)
    (x : E) : 0 ≤ re ⟪T x, x⟫ :=
  hT.2 x

theorem IsPositive.re_inner_nonneg_right {T : E →ₗ[𝕜] E} (hT : IsPositive T)
    (x : E) : 0 ≤ re ⟪x, T x⟫ :=
  inner_re_symm (𝕜 := 𝕜) _ x ▸ hT.re_inner_nonneg_left x

section Complex

variable {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℂ E']

theorem isPositive_iff_complex (T : E' →ₗ[ℂ] E') :
    IsPositive T ↔ ∀ x, (re ⟪T x, x⟫_ℂ : ℂ) = ⟪T x, x⟫_ℂ ∧ 0 ≤ re ⟪T x, x⟫_ℂ := by
  simp_rw [IsPositive, forall_and, isSymmetric_iff_inner_map_self_real,
    conj_eq_iff_re, re_to_complex, Complex.coe_algebraMap]

end Complex

theorem IsPositive.isSelfAdjoint [FiniteDimensional 𝕜 E] {T : E →ₗ[𝕜] E} (hT : IsPositive T) :
    IsSelfAdjoint T := (isSymmetric_iff_isSelfAdjoint _).mp hT.isSymmetric

theorem IsPositive.adjoint_eq [FiniteDimensional 𝕜 E] {T : E →ₗ[𝕜] E} (hT : IsPositive T) :
    T.adjoint = T := hT.isSelfAdjoint

theorem isPositive_iff (T : E →ₗ[𝕜] E) :
    IsPositive T ↔ IsSymmetric T ∧ ∀ x, 0 ≤ ⟪T x, x⟫ := by
  simp_rw [IsPositive, and_congr_right_iff, ← RCLike.ofReal_nonneg (K := 𝕜)]
  intro hT
  simp [hT]

theorem IsPositive.inner_nonneg_left {T : E →ₗ[𝕜] E} (hT : IsPositive T) (x : E) : 0 ≤ ⟪T x, x⟫ :=
  (T.isPositive_iff.mp hT).right x

theorem IsPositive.inner_nonneg_right {T : E →ₗ[𝕜] E} (hT : IsPositive T) (x : E) :
    0 ≤ ⟪x, T x⟫ :=
  hT.isSymmetric _ _ ▸ hT.inner_nonneg_left x
