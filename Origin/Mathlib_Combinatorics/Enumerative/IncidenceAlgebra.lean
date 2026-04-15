/-
Extracted from Combinatorics/Enumerative/IncidenceAlgebra.lean
Genuine: 2 of 4 | Dissolved: 1 | Infrastructure: 1
-/
import Origin.Core

/-!
# Incidence algebras

Given a locally finite order `α` the incidence algebra over `α` is the type of functions from
non-empty intervals of `α` to some algebraic codomain.

This algebra has a natural multiplication operation whereby the product of two such functions
is defined on an interval by summing over all divisions into two subintervals the product of the
values of the original pair of functions.

This structure allows us to interpret many natural invariants of the intervals (such as their
cardinality) as elements of the incidence algebra. For instance the cardinality function, viewed as
an element of the incidence algebra, is simply the square of the function that takes constant value
one on all intervals. This constant function is called the zeta function, after
its connection with the Riemann zeta function.

The incidence algebra is a good setting for proving many inclusion-exclusion type principles, these
go under the name Möbius inversion, and are essentially due to the fact that the zeta function has
a multiplicative inverse in the incidence algebra, an inductively definable function called the
Möbius function that generalizes the Möbius function in number theory.

## Main definitions

* `1 : IncidenceAlgebra 𝕜 α` is the delta function, defined analogously to the identity matrix.
* `f * g` is the incidence algebra product, defined analogously to the matrix product.
* `IncidenceAlgebra.zeta` is the zeta function, defined analogously to the upper triangular matrix
  of ones.
* `IncidenceAlgebra.mu` is the inverse of the zeta function.

## Implementation notes

One has to define `mu` as either the left or right inverse of `zeta`. We define it as the left
inverse, and prove it is also a right inverse by defining `mu'` as the right inverse and using that
left and right inverses agree if they exist.

## TODOs

Here are some additions to this file that could be made in the future:
- Generalize the construction of `mu` to invert any element of the incidence algebra `f` which has
  `f x x` a unit for all `x`.
- Give formulas for higher powers of zeta.
- A formula for the möbius function on a pi type similar to the one for products
- More examples / applications to different posets.
- Connection with Galois insertions
- Finsum version of Möbius inversion that holds even when an order doesn't have top/bot?
- Connect this theory to (infinite) matrices, giving maps of the incidence algebra to matrix rings
- Connect to the more advanced theory of arithmetic functions, and Dirichlet convolution.

## References

* [Aigner, *Combinatorial Theory, Chapter IV*][aigner1997]
* [Jacobson, *Basic Algebra I, 8.6*][jacobson1974]
* [Doubilet, Rota, Stanley, *On the foundations of Combinatorial Theory
  VI*][doubilet_rota_stanley_vi]
* [Spiegel, O'Donnell, *Incidence Algebras*][spiegel_odonnell1997]
* [Kung, Rota, Yan, *Combinatorics: The Rota Way, Chapter 3*][kung_rota_yan2009]
-/

open Finset OrderDual

variable {F 𝕜 𝕝 𝕞 α β : Type*}

structure IncidenceAlgebra (𝕜 α : Type*) [Zero 𝕜] [LE α] where
  /-- The underlying function of an element of the incidence algebra.

  Do not use this function directly. Instead use the coercion coming from the `FunLike`
  instance. -/
  toFun : α → α → 𝕜
  eq_zero_of_not_le' ⦃a b : α⦄ : ¬a ≤ b → toFun a b = 0

namespace IncidenceAlgebra

section Zero

variable [Zero 𝕜] [LE α] {a b : α}

-- INSTANCE (free from Core): instFunLike

lemma apply_eq_zero_of_not_le (h : ¬a ≤ b) (f : IncidenceAlgebra 𝕜 α) : f a b = 0 :=
  eq_zero_of_not_le' _ h

-- DISSOLVED: le_of_ne_zero

section Coes

initialize_simps_projections IncidenceAlgebra (toFun → apply)
