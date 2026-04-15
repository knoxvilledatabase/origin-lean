/-
Extracted from Algebra/Lie/Loop.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Loop Lie algebras and their central extensions
Given a Lie algebra `L`, the loop algebra is the Lie algebra of maps from a circle into `L`. This
can mean many different things, e.g., continuous maps, smooth maps, polynomial maps. In this file,
we consider the simplest case of polynomial maps, meaning we take a base change with the ring of
Laurent polynomials.

Loop Lie algebras admit central extensions attached to invariant inner products on the base Lie
algebra. When the base Lie algebra is finite dimensional and simple, the corresponding central
extension (with an outer derivation attached) admits an infinite root system with affine Weyl group.
These extended Lie algebras are called untwisted affine Kac-Moody Lie algebras.

We implement the basic theory using `AddMonoidAlgebra` instead of `LaurentPolynomial` for
flexibility. The classical loop algebra is then written `loopAlgebra R ℤ L`.

## Main definitions
* `LieAlgebra.loopAlgebra`: The tensor product of a Lie algebra with an `AddMonoidAlgebra`.
* `LieAlgebra.loopAlgebra.toFinsupp`: A linear equivalence from the loop algebra to the space of
  finitely supported functions.
* `LieAlgebra.loopAlgebra.twoCochainOfBilinear`: The 2-cochain for a loop algebra with trivial
  coefficients attached to a symmetric bilinear form on the base Lie algebra.
* `LieAlgebra.loopAlgebra.twoCocycleOfBilinear`: The 2-cocycle for a loop algebra with trivial
  coefficients attached to a symmetric invariant bilinear form on the base Lie algebra.

## TODO
* Evaluation representations
* Construction of central extensions from invariant forms.
* Positive energy representations induced from a fixed central character

## Tags
lie ring, lie algebra, base change, Laurent polynomial
-/

noncomputable section

open scoped TensorProduct

variable (R A L : Type*)

namespace LieAlgebra

variable [CommRing R] [LieRing L] [LieAlgebra R L]

abbrev loopAlgebra := AddMonoidAlgebra R A ⊗[R] L

open LaurentPolynomial in

def loopAlgebraEquivLaurent :
    loopAlgebra R ℤ L ≃ₗ⁅R⁆ R[T;T⁻¹] ⊗[R] L :=
  LieEquiv.refl

namespace LoopAlgebra

open Classical in

def toFinsupp : loopAlgebra R A L ≃ₗ[R] A →₀ L :=
  TensorProduct.equivFinsuppOfBasisLeft (AddMonoidAlgebra.basis A R)
