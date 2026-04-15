/-
Extracted from Topology/Algebra/ConstMulAction.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Monoid actions continuous in the second variable

In this file we define class `ContinuousConstSMul`. We say `ContinuousConstSMul Γ T` if
`Γ` acts on `T` and for each `γ`, the map `x ↦ γ • x` is continuous. (This differs from
`ContinuousSMul`, which requires simultaneous continuity in both variables.)

## Main definitions

* `ContinuousConstSMul Γ T` : typeclass saying that the map `x ↦ γ • x` is continuous on `T`;
* `ProperlyDiscontinuousSMul`: says that the scalar multiplication `(•) : Γ → T → T`
  is properly discontinuous, that is, for any pair of compact sets `K, L` in `T`, only finitely
  many `γ:Γ` move `K` to have nontrivial intersection with `L`.
* `Homeomorph.smul`: scalar multiplication by an element of a group `Γ` acting on `T`
  is a homeomorphism of `T`.
* `Homeomorph.smulOfNeZero`: if a group with zero `G₀` (e.g., a field) acts on `X` and `c : G₀`
  is a nonzero element of `G₀`, then scalar multiplication by `c` is a homeomorphism of `X`;
* `Homeomorph.smul`: scalar multiplication by an element of a group `G` acting on `X`
  is a homeomorphism of `X`.

## Main results

* `isOpenMap_quotient_mk'_mul` : The quotient map by a group action is open.
* `t2Space_of_properlyDiscontinuousSMul_of_t2Space` : The quotient by a discontinuous group
  action of a locally compact T₂ space is T₂.

## Tags

Hausdorff, discrete group, properly discontinuous, quotient space

-/

assert_not_exists IsOrderedRing

open Topology Pointwise Filter Set TopologicalSpace

class ContinuousConstSMul (Γ : Type*) (T : Type*) [TopologicalSpace T] [SMul Γ T] : Prop where
  /-- The scalar multiplication `(•) : Γ → T → T` is continuous in the second argument. -/
  continuous_const_smul : ∀ γ : Γ, Continuous fun x : T => γ • x

class ContinuousConstVAdd (Γ : Type*) (T : Type*) [TopologicalSpace T] [VAdd Γ T] : Prop where
  /-- The additive action `(+ᵥ) : Γ → T → T` is continuous in the second argument. -/
  continuous_const_vadd : ∀ γ : Γ, Continuous fun x : T => γ +ᵥ x

attribute [to_additive] ContinuousConstSMul

export ContinuousConstSMul (continuous_const_smul)

export ContinuousConstVAdd (continuous_const_vadd)

variable {M α β : Type*}

section SMul

variable [TopologicalSpace α] [SMul M α] [ContinuousConstSMul M α]
