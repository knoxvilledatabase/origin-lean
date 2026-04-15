/-
Extracted from Algebra/Polynomial/Laurent.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!  # Laurent polynomials

We introduce Laurent polynomials over a semiring `R`.  Mathematically, they are expressions of the
form
$$
\sum_{i \in \mathbb{Z}} a_i T ^ i
$$
where the sum extends over a finite subset of `ℤ`.  Thus, negative exponents are allowed.  The
coefficients come from the semiring `R` and the variable `T` commutes with everything.

Since we are going to convert back and forth between polynomials and Laurent polynomials, we
decided to maintain some distinction by using the symbol `T`, rather than `X`, as the variable for
Laurent polynomials.

## Notation
The symbol `R[T;T⁻¹]` stands for `LaurentPolynomial R`.  We also define

* `C : R →+* R[T;T⁻¹]` the inclusion of constant polynomials, analogous to the one for `R[X]`;
* `T : ℤ → R[T;T⁻¹]` the sequence of powers of the variable `T`.

## Implementation notes

We define Laurent polynomials as `AddMonoidAlgebra R ℤ`.
Thus, they are essentially `Finsupp`s `ℤ →₀ R`.
This choice differs from the current irreducible design of `Polynomial`, that instead shields away
the implementation via `Finsupp`s.  It is closer to the original definition of polynomials.

As a consequence, `LaurentPolynomial` plays well with polynomials, but there is a little roughness
in establishing the API, since the `Finsupp` implementation of `R[X]` is well-shielded.

Unlike the case of polynomials, I felt that the exponent notation was not too easy to use, as only
natural exponents would be allowed.  Moreover, in the end, it seems likely that we should aim to
perform computations on exponents in `ℤ` anyway and separating this via the symbol `T` seems
convenient.

I made a *heavy* use of `simp` lemmas, aiming to bring Laurent polynomials to the form `C a * T n`.
Any comments or suggestions for improvements is greatly appreciated!

## Future work
Lots is missing!
-- (Riccardo) add inclusion into Laurent series.
-- A "better" definition of `trunc` would be as an `R`-linear map.  This works:
--  ```
--  def trunc : R[T;T⁻¹] →[R] R[X] :=
--    refine (?_ : R[ℕ] →[R] R[X]).comp ?_
--    · exact ⟨(toFinsuppIso R).symm, by simp⟩
--    · refine ⟨fun r ↦ comapDomain _ r
--        (Set.injOn_of_injective (fun _ _ ↦ Int.ofNat.inj) _), ?_⟩
--      exact fun r f ↦ comapDomain_smul ..
--  ```
--  but it would make sense to bundle the maps better, for a smoother user experience.
--  I (DT) did not have the strength to embark on this (possibly short!) journey, after getting to
--  this stage of the Laurent process!
--  This would likely involve adding a `comapDomain` analogue of
--  `AddMonoidAlgebra.mapDomainAlgHom` and an `R`-linear version of
--  `Polynomial.toFinsuppIso`.
-- Add `degree, intDegree, intTrailingDegree, leadingCoeff, trailingCoeff,...`.
-/

open Polynomial Function AddMonoidAlgebra Finsupp

noncomputable section

variable {R S : Type*}

abbrev LaurentPolynomial (R : Type*) [Semiring R] :=
  AddMonoidAlgebra R ℤ
