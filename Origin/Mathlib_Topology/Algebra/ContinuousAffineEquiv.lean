/-
Extracted from Topology/Algebra/ContinuousAffineEquiv.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Continuous affine equivalences

In this file, we define continuous affine equivalences, affine equivalences
which are continuous with continuous inverse.

## Main definitions
* `ContinuousAffineEquiv.refl k P`: the identity map as a `ContinuousAffineEquiv`;
* `e.symm`: the inverse map of a `ContinuousAffineEquiv` as a `ContinuousAffineEquiv`;
* `e.trans e'`: composition of two `ContinuousAffineEquiv`s; note that the order
  follows `mathlib`'s `CategoryTheory` convention (apply `e`, then `e'`),
  not the convention used in function composition and compositions of bundled morphisms.

* `e.toHomeomorph`: the continuous affine equivalence `e` as a homeomorphism
* `e.toContinuousAffineMap`: the continuous affine equivalence `e` as a continuous affine map
* `ContinuousLinearEquiv.toContinuousAffineEquiv`: a continuous linear equivalence as a continuous
  affine equivalence
* `ContinuousAffineEquiv.constVAdd`: `AffineEquiv.constVAdd` as a continuous affine equivalence

## TODO
- equip `ContinuousAffineEquiv k P P` with a `Group` structure,
  with multiplication corresponding to composition in `AffineEquiv.group`.

-/

open Function

structure ContinuousAffineEquiv (k P₁ P₂ : Type*) {V₁ V₂ : Type*} [Ring k]
    [AddCommGroup V₁] [Module k V₁] [AddTorsor V₁ P₁] [TopologicalSpace P₁]
    [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂] [TopologicalSpace P₂]
    extends P₁ ≃ᵃ[k] P₂ where
  continuous_toFun : Continuous toFun := by fun_prop
  continuous_invFun : Continuous invFun := by fun_prop
