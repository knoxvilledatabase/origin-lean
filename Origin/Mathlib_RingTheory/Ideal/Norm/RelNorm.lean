/-
Extracted from RingTheory/Ideal/Norm/RelNorm.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Ideal norms

This file defines the relative ideal norm `Ideal.spanNorm R (I : Ideal S) : Ideal S` as the ideal
spanned by the norms of elements in `I`.

## Main definitions

* `Ideal.spanNorm R (I : Ideal S)`: the ideal spanned by the norms of elements in `I`.
  This is used to define `Ideal.relNorm`.
* `Ideal.relNorm R (I : Ideal S)`: the relative ideal norm as a bundled monoid-with-zero morphism,
  defined as the ideal spanned by the norms of elements in `I`.

## Main results

* `map_mul Ideal.relNorm`: multiplicativity of the relative ideal norm
* `relNorm_relNorm`: transitivity of the relative ideal norm

-/

open Module

open scoped nonZeroDivisors

section SpanNorm

namespace Ideal

open Submodule

variable (R S : Type*) [CommRing R] [IsDomain R] {S : Type*} [CommRing S] [IsDomain S]

variable [IsIntegrallyClosed R] [IsIntegrallyClosed S] [Algebra R S] [Module.Finite R S]

variable [IsTorsionFree R S]

attribute [local instance] FractionRing.liftAlgebra

noncomputable def spanNorm (I : Ideal S) : Ideal R :=
  Ideal.map (Algebra.intNorm R S) I
