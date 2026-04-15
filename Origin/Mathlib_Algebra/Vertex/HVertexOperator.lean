/-
Extracted from Algebra/Vertex/HVertexOperator.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Vertex operators
In this file we introduce heterogeneous vertex operators using Hahn series.  When `R = ℂ`, `V = W`,
and `Γ = ℤ`, then this is the usual notion of "meromorphic left-moving 2D field".  The notion we use
here allows us to consider composites and scalar-multiply by multivariable Laurent series.
## Definitions
* `HVertexOperator` : An `R`-linear map from an `R`-module `V` to `HahnModule Γ W`.
* The coefficient function as an `R`-linear map.
* Composition of heterogeneous vertex operators - values are Hahn series on lex order product.
## Main results
* Ext
## TODO
* curry for tensor product inputs
* more API to make ext comparisons easier.
* formal variable API, e.g., like the `T` function for Laurent polynomials.
## References

* [R. Borcherds, *Vertex Algebras, Kac-Moody Algebras, and the Monster*][borcherds1986vertex]

-/

assert_not_exists Cardinal

noncomputable section

variable {Γ : Type*} [PartialOrder Γ] {R : Type*} {V W : Type*} [CommRing R]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

abbrev HVertexOperator (Γ : Type*) [PartialOrder Γ] (R : Type*) [CommRing R]
    (V : Type*) (W : Type*) [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W] :=
  V →ₗ[R] (HahnModule Γ R W)

namespace HVertexOperator

section Coeff

open HahnModule
