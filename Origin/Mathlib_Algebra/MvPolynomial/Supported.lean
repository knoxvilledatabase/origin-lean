/-
Extracted from Algebra/MvPolynomial/Supported.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Polynomials supported by a set of variables

This file contains the definition and lemmas about `MvPolynomial.supported`.

## Main definitions

* `MvPolynomial.supported` : Given a set `s : Set σ`, `supported R s` is the subalgebra of
  `MvPolynomial σ R` consisting of polynomials whose set of variables is contained in `s`.
  This subalgebra is isomorphic to `MvPolynomial s R`.

## Tags
variables, polynomial, vars
-/

universe u v w

namespace MvPolynomial

variable {σ : Type*} {R : Type u}

section CommSemiring

variable [CommSemiring R] {p : MvPolynomial σ R}

variable (R) in

noncomputable def supported (s : Set σ) : Subalgebra R (MvPolynomial σ R) :=
  Algebra.adjoin R (X '' s)

open Algebra

theorem supported_eq_range_rename (s : Set σ) : supported R s = (rename ((↑) : s → σ)).range := by
  rw [supported, Set.image_eq_range, adjoin_range_eq_range_aeval, rename]
  congr

noncomputable def supportedEquivMvPolynomial (s : Set σ) : supported R s ≃ₐ[R] MvPolynomial s R :=
  (Subalgebra.equivOfEq _ _ (supported_eq_range_rename s)).trans
    (AlgEquiv.ofInjective (rename ((↑) : s → σ)) (rename_injective _ Subtype.val_injective)).symm
