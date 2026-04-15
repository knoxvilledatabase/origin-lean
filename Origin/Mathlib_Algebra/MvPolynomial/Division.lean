/-
Extracted from Algebra/MvPolynomial/Division.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Division of `MvPolynomial` by monomials

## Main definitions

* `MvPolynomial.divMonomial x s`: divides `x` by the monomial `MvPolynomial.monomial 1 s`
* `MvPolynomial.modMonomial x s`: the remainder upon dividing `x` by the monomial
  `MvPolynomial.monomial 1 s`.

## Main results

* `MvPolynomial.divMonomial_add_modMonomial`, `MvPolynomial.modMonomial_add_divMonomial`:
  `divMonomial` and `modMonomial` are well-behaved as quotient and remainder operators.

## Implementation notes

Where possible, the results in this file should be first proved in the generality of
`AddMonoidAlgebra`, and then the versions specialized to `MvPolynomial` proved in terms of these.

-/

variable {σ R : Type*} [CommSemiring R]

namespace MvPolynomial

section CopiedDeclarations

/-! Please ensure the declarations in this section are direct translations of `AddMonoidAlgebra`
results. -/

noncomputable def divMonomial (p : MvPolynomial σ R) (s : σ →₀ ℕ) : MvPolynomial σ R :=
  AddMonoidAlgebra.divOf p s

local infixl:70 " /ᵐᵒⁿᵒᵐⁱᵃˡ " => divMonomial
