/-
Extracted from RingTheory/Polynomial/Dickson.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Dickson polynomials

The (generalised) Dickson polynomials are a family of polynomials indexed by `ℕ × ℕ`,
with coefficients in a commutative ring `R` depending on an element `a∈R`. More precisely, the
they satisfy the recursion `dickson k a (n + 2) = X * (dickson k a n + 1) - a * (dickson k a n)`
with starting values `dickson k a 0 = 3 - k` and `dickson k a 1 = X`. In the literature,
`dickson k a n` is called the `n`-th Dickson polynomial of the `k`-th kind associated to the
parameter `a : R`. They are closely related to the Chebyshev polynomials in the case that `a=1`.
When `a=0` they are just the family of monomials `X ^ n`.

## Main definition

* `Polynomial.dickson`: the generalised Dickson polynomials.

## Main statements

* `Polynomial.dickson_one_one_mul`, the `(m * n)`-th Dickson polynomial of the first kind for
  parameter `1 : R` is the composition of the `m`-th and `n`-th Dickson polynomials of the first
  kind for `1 : R`.
* `Polynomial.dickson_one_one_charP`, for a prime number `p`, the `p`-th Dickson polynomial of the
  first kind associated to parameter `1 : R` is congruent to `X ^ p` modulo `p`.

## References

* [R. Lidl, G. L. Mullen and G. Turnwald, _Dickson polynomials_][MR1237403]

## TODO

* Redefine `dickson` in terms of `LinearRecurrence`.
* Show that `dickson 2 1` is equal to the characteristic polynomial of the adjacency matrix of a
  type A Dynkin diagram.
* Prove that the adjacency matrices of simply laced Dynkin diagrams are precisely the adjacency
  matrices of simple connected graphs which annihilate `dickson 2 1`.
-/

noncomputable section

namespace Polynomial

variable {R S : Type*} [CommRing R] [CommRing S] (k : ℕ) (a : R)

noncomputable def dickson : ℕ → R[X]
  | 0 => 3 - k
  | 1 => X
  | n + 2 => X * dickson (n + 1) - C a * dickson n
