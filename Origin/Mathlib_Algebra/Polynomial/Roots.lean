/-
Extracted from Algebra/Polynomial/Roots.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Theory of univariate polynomials

We define the multiset of roots of a polynomial, and prove basic results about it.

## Main definitions

* `Polynomial.roots p`: The multiset containing all the roots of `p`, including their
  multiplicities.
* `Polynomial.rootSet p E`: The set of distinct roots of `p` in an algebra `E`.

## Main statements

* `Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C`: If a polynomial has as many roots as its
  degree, it can be written as the product of its leading coefficient with `∏ (X - a)` where `a`
  ranges through its roots.

-/

assert_not_exists Ideal

open Multiset Finset

noncomputable section

namespace Polynomial

universe u v w z

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

section CommRing

variable [CommRing R] [IsDomain R] {p q : R[X]}

section Roots

noncomputable def roots (p : R[X]) : Multiset R :=
  haveI := Classical.decEq R
  haveI := Classical.dec (p = 0)
  if h : p = 0 then ∅ else Classical.choose (exists_multiset_roots h)

theorem roots_def [DecidableEq R] (p : R[X]) [Decidable (p = 0)] :
    p.roots = if h : p = 0 then ∅ else Classical.choose (exists_multiset_roots h) := by
  rename_i iR ip0
  obtain rfl := Subsingleton.elim iR (Classical.decEq R)
  obtain rfl := Subsingleton.elim ip0 (Classical.dec (p = 0))
  rfl
