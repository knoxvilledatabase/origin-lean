/-
Extracted from Analysis/Calculus/ImplicitFunction/ProdDomain.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Implicit function theorem — domain a product space

This specialization of the implicit function theorem applies to an uncurried bivariate function
`f : E₁ × E₂ → F` and assumes strict differentiability of `f` at `u : E₁ × E₂` as well as
invertibility of `f₂u : E₂ →L[𝕜] F` its partial derivative with respect to the second argument.

It proves the existence of `ψ : E₁ → E₂` such that for `v` in a neighbourhood of `u` we have
`f v = f u ↔ ψ v.1 = v.2`. This is `HasStrictFDerivAt.implicitFunctionOfProdDomain`. A formula for
its first derivative follows.

## Tags

implicit function
-/

open Filter

open scoped Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] [CompleteSpace E₁]
  {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂] [CompleteSpace E₂]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

namespace HasStrictFDerivAt

variable {u : E₁ × E₂} {f : E₁ × E₂ → F} {f'u : E₁ × E₂ →L[𝕜] F}

def implicitFunctionDataOfProdDomain
    (dfu : HasStrictFDerivAt f f'u u) (if₂u : (f'u ∘L .inr 𝕜 E₁ E₂).IsInvertible) :
    ImplicitFunctionData 𝕜 (E₁ × E₂) F E₁ where
  leftFun := f
  rightFun := Prod.fst
  pt := u
  leftDeriv := f'u
  hasStrictFDerivAt_leftFun := dfu
  rightDeriv := .fst 𝕜 E₁ E₂
  hasStrictFDerivAt_rightFun := hasStrictFDerivAt_fst
  range_leftDeriv := by
    have : (f'u ∘L .inr 𝕜 E₁ E₂).range ≤ f'u.range := LinearMap.range_comp_le_range ..
    rwa [LinearMap.range_eq_top.mpr if₂u.surjective, top_le_iff] at this
  range_rightDeriv := Submodule.range_fst
  isCompl_ker := by
    constructor
    · rw [LinearMap.disjoint_ker]
      intro (_, y) h rfl
      simpa using (injective_iff_map_eq_zero _).mp if₂u.injective y h
    · rw [Submodule.codisjoint_iff_exists_add_eq]
      intro v
      have ⟨y, hy⟩ := if₂u.surjective (f'u v)
      use v - (0, y), (0, y)
      aesop
