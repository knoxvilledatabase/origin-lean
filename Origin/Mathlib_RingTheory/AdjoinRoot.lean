/-
Extracted from RingTheory/AdjoinRoot.lean
Genuine: 2 of 5 | Dissolved: 1 | Infrastructure: 2
-/
import Origin.Core

/-!
# Adjoining roots of polynomials

This file defines the commutative ring `AdjoinRoot f`, the ring R[X]/(f) obtained from a
commutative ring `R` and a polynomial `f : R[X]`. If furthermore `R` is a field and `f` is
irreducible, the field structure on `AdjoinRoot f` is constructed.

We suggest stating results on `IsAdjoinRoot` instead of `AdjoinRoot` to achieve higher
generality, since `IsAdjoinRoot` works for all different constructions of `R[α]`
including `AdjoinRoot f = R[X]/(f)` itself.

## Main definitions and results

The main definitions are in the `AdjoinRoot` namespace.

*  `mk f : R[X] →+* AdjoinRoot f`, the natural ring homomorphism.

*  `of f : R →+* AdjoinRoot f`, the natural ring homomorphism.

* `root f : AdjoinRoot f`, the image of X in R[X]/(f).

* `lift (i : R →+* S) (x : S) (h : f.eval₂ i x = 0) : (AdjoinRoot f) →+* S`, the ring
  homomorphism from R[X]/(f) to S extending `i : R →+* S` and sending `X` to `x`.

* `lift_hom (x : S) (hfx : aeval x f = 0) : AdjoinRoot f →ₐ[R] S`, the algebra
  homomorphism from R[X]/(f) to S extending `algebraMap R S` and sending `X` to `x`

* `equiv : (AdjoinRoot f →ₐ[F] E) ≃ {x // x ∈ f.aroots E}` a
  bijection between algebra homomorphisms from `AdjoinRoot` and roots of `f` in `S`

-/

noncomputable section

open Algebra (FinitePresentation FiniteType)

open Ideal Module Polynomial

variable {R S T U K : Type*}

def AdjoinRoot [CommRing R] (f : R[X]) : Type _ :=
  Polynomial R ⧸ (span {f} : Ideal R[X])

namespace AdjoinRoot

section CommRing

variable [CommRing R] (f g : R[X])

-- INSTANCE (free from Core): CommRing,

-- INSTANCE (free from Core): :

-- DISSOLVED: nontrivial

def mk : R[X] →+* AdjoinRoot f :=
  Ideal.Quotient.mk _
