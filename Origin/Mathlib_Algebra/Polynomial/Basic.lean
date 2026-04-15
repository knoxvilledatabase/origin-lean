/-
Extracted from Algebra/Polynomial/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Theory of univariate polynomials

This file defines `Polynomial R`, the type of univariate polynomials over the semiring `R`, builds
a semiring structure on it, and gives basic definitions that are expanded in other files in this
directory.

## Main definitions

* `monomial n a` is the polynomial `a X^n`. Note that `monomial n` is defined as an `R`-linear map.
* `C a` is the constant polynomial `a`. Note that `C` is defined as a ring homomorphism.
* `X` is the polynomial `X`, i.e., `monomial 1 1`.
* `p.sum f` is `∑ n ∈ p.support, f n (p.coeff n)`, i.e., one sums the values of functions applied
  to coefficients of the polynomial `p`.
* `p.erase n` is the polynomial `p` in which one removes the `c X^n` term.
* `ofMultiset s` is the monic polynomial `p` which has roots `s`.

There are often two natural variants of lemmas involving sums, depending on whether one acts on the
polynomials, or on the function. The naming convention is that one adds `index` when acting on
the polynomials. For instance,
* `sum_add_index` states that `(p + q).sum f = p.sum f + q.sum f`;
* `sum_add` states that `p.sum (fun n x ↦ f n x + g n x) = p.sum f + p.sum g`.
* Notation to refer to `Polynomial R`, as `R[X]` or `R[t]`.

## Implementation

Polynomials are defined using `R[ℕ]`, where `R` is a semiring.
The variable `X` commutes with every polynomial `p`: lemma `X_mul` proves the identity
`X * p = p * X`.  The relationship to `R[ℕ]` is through a structure
to make polynomials irreducible from the point of view of the kernel. Most operations
are irreducible since Lean cannot compute anyway with `AddMonoidAlgebra`. There are two
exceptions that we make semireducible:
* The zero polynomial, so that its coefficients are definitionally equal to `0`.
* The scalar action, to permit typeclass search to unfold it to resolve potential instance
  diamonds.

The raw implementation of the equivalence between `R[X]` and `R[ℕ]` is
done through `ofFinsupp` and `toFinsupp` (or, equivalently, `rcases p` when `p` is a polynomial
gives an element `q` of `R[ℕ]`, and conversely `⟨q⟩` gives back `p`). The
equivalence is also registered as a ring equiv in `Polynomial.toFinsuppIso`. These should
in general not be used once the basic API for polynomials is constructed.
-/

noncomputable section

structure Polynomial (R : Type*) [Semiring R] where ofFinsupp ::
  /-- The coefficients `ℕ →₀ R` of a polynomial in `R[X]`. -/
  toFinsupp : AddMonoidAlgebra R ℕ
