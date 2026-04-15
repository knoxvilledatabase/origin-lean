/-
Extracted from LinearAlgebra/AffineSpace/AffineMap.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Affine maps

This file defines affine maps.

## Main definitions

* `AffineMap` is the type of affine maps between two affine spaces with the same ring `k`.  Various
  basic examples of affine maps are defined, including `const`, `id`, `lineMap` and `homothety`.

## Notation

* `P1 →ᵃ[k] P2` is a notation for `AffineMap k P1 P2`;
* `AffineSpace V P`: a localized notation for `AddTorsor V P` defined in
  `LinearAlgebra.AffineSpace.Basic`.

## Implementation notes

`outParam` is used in the definition of `[AddTorsor V P]` to make `V` an implicit argument
(deduced from `P`) in most cases. As for modules, `k` is an explicit argument rather than implied by
`P` or `V`.

This file only provides purely algebraic definitions and results. Those depending on analysis or
topology are defined elsewhere; see `Analysis.Normed.Affine.AddTorsor` and
`Topology.Algebra.Affine`.

## References

* https://en.wikipedia.org/wiki/Affine_space
* https://en.wikipedia.org/wiki/Principal_homogeneous_space
-/

open Affine Module

structure AffineMap (k : Type*) {V1 : Type*} (P1 : Type*) {V2 : Type*} (P2 : Type*) [Ring k]
  [AddCommGroup V1] [Module k V1] [AffineSpace V1 P1] [AddCommGroup V2] [Module k V2]
  [AffineSpace V2 P2] where
  /-- The underlying function between the affine spaces `P1` and `P2`. -/
  toFun : P1 → P2
  /-- The linear map between the corresponding vector spaces `V1` and `V2`.
  This represents how the affine map acts on differences of points. -/
  linear : V1 →ₗ[k] V2
  map_vadd' : ∀ (p : P1) (v : V1), toFun (v +ᵥ p) = linear v +ᵥ toFun p

notation:25 P1 " →ᵃ[" k:25 "] " P2:0 => AffineMap k P1 P2

-- INSTANCE (free from Core): AffineMap.instFunLike

namespace LinearMap

variable {k : Type*} {V₁ : Type*} {V₂ : Type*} [Ring k] [AddCommGroup V₁] [Module k V₁]
  [AddCommGroup V₂] [Module k V₂] (f : V₁ →ₗ[k] V₂)

def toAffineMap : V₁ →ᵃ[k] V₂ where
  toFun := f
  linear := f
  map_vadd' p v := f.map_add v p
