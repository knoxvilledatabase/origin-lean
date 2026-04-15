/-
Extracted from Geometry/Convex/Cone/TensorProduct.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Tensor products of cones

Given ordered modules `M` and `N`, there are in general several distinct possible
orderings of the tensor product module `M ⊗ N`. Since the ordering of an ordered module
can be represented by its cone of nonnegative elements, there are likewise multiple
ways to construct a cone in `M ⊗ N` from cones in `M` and `N`. Such constructions
are referred to as tensor products of cones.

"Sufficiently nice" candidates for tensor products of cones are bounded by the minimal
and maximal tensor products. These products are generally distinct but coincide in special cases.

We define the minimal and maximal tensor products of pointed cones:

* `minTensorProduct C₁ C₂`: all conical combinations of elementary tensor products
  `x ⊗ₜ y` with `x ∈ C₁` and `y ∈ C₂`.
* `maxTensorProduct C₁ C₂`: the dual cone of the minimal tensor product of the dual cones.

## Main results

* `minTensorProduct_le_maxTensorProduct`: the minimal tensor product
  is less than or equal to the maximal tensor product

## Notation

* no special notation defined
* x, y, z are elements of the (original) cones
* φ, ψ are elements of the dual cones

## References

* [Aubrun et al. *Entangleability of cones*][aubrunEntangleabilityCones2021]

-/

open TensorProduct Module

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

variable {G : Type*} [AddCommGroup G] [Module R G]

variable {H : Type*} [AddCommGroup H] [Module R H]

namespace PointedCone

noncomputable def minTensorProduct (C₁ : PointedCone R G) (C₂ : PointedCone R H) :
    PointedCone R (G ⊗[R] H) :=
  .hull R (.image2 (· ⊗ₜ[R] ·) C₁ C₂)

noncomputable def maxTensorProduct (C₁ : PointedCone R G) (C₂ : PointedCone R H) :
    PointedCone R (G ⊗[R] H) :=
  .dual (dualDistrib R G H) (minTensorProduct (.dual (dualPairing R G).flip C₁)
    (.dual (dualPairing R H).flip C₂))
