/-
Extracted from Algebra/MonoidAlgebra/Division.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Division of `AddMonoidAlgebra` by monomials

This file is most important for when `G = ℕ` (polynomials) or `G = σ →₀ ℕ` (multivariate
polynomials).

In order to apply in maximal generality (such as for `LaurentPolynomial`s), this uses
`∃ d, g' = g + d` in many places instead of `g ≤ g'`.

## Main definitions

* `AddMonoidAlgebra.divOf x g`: divides `x` by the monomial `AddMonoidAlgebra.of k G g`
* `AddMonoidAlgebra.modOf x g`: the remainder upon dividing `x` by the monomial
  `AddMonoidAlgebra.of k G g`.

## Main results

* `AddMonoidAlgebra.divOf_add_modOf`, `AddMonoidAlgebra.modOf_add_divOf`: `divOf` and
  `modOf` are well-behaved as quotient and remainder operators.

## Implementation notes

`∃ d, g' = g + d` is used as opposed to some other permutation up to commutativity in order to match
the definition of `semigroupDvd`. The results in this file could be duplicated for
`MonoidAlgebra` by using `g ∣ g'`, but this can't be done automatically, and in any case is not
likely to be very useful.

-/

variable {k G : Type*} [Semiring k]

namespace AddMonoidAlgebra

variable [AddCommMonoid G]

noncomputable def divOf [IsCancelAdd G] (x : k[G]) (g : G) : k[G] :=
  -- note: comapping by `+ g` has the effect of subtracting `g` from every element in
  -- the support, and discarding the elements of the support from which `g` can't be subtracted.
  -- If `G` is an additive group, such as `ℤ` when used for `LaurentPolynomial`,
  -- then no discarding occurs.
  @Finsupp.comapDomain.addMonoidHom _ _ _ _ (g + ·) (add_right_injective g) x

local infixl:70 " /ᵒᶠ " => divOf

section divOf

variable [IsCancelAdd G]
