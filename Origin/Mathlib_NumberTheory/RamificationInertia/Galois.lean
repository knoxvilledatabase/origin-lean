/-
Extracted from NumberTheory/RamificationInertia/Galois.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Ramification theory in Galois extensions of Dedekind domains

In this file, we discuss the ramification theory in Galois extensions of Dedekind domains, which is
  also called Hilbert's Ramification Theory.

Assume `B / A` is a finite extension of Dedekind domains, `K` is the fraction ring of `A`,
  `L` is the fraction ring of `K`, `L / K` is a Galois extension.

## Main definitions

* `Ideal.ramificationIdxIn`: It can be seen from
  the theorem `Ideal.ramificationIdx_eq_of_isGaloisGroup` that all `Ideal.ramificationIdx` over a
  fixed maximal ideal `p` of `A` are the same, which we define as `Ideal.ramificationIdxIn`.

* `Ideal.inertiaDegIn`: It can be seen from
  the theorem `Ideal.inertiaDeg_eq_of_isGaloisGroup` that all `Ideal.inertiaDeg` over a fixed
  maximal ideal `p` of `A` are the same, which we define as `Ideal.inertiaDegIn`.

## Main results

* `Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn`: Let `p` be a prime of `A`,
  `r` be the number of prime ideals lying over `p`, `e` be the ramification index of `p` in `B`,
  and `f` be the inertia degree of `p` in `B`. Then `r * (e * f) = [L : K]`. It is the form of the
  `Ideal.sum_ramification_inertia` in the case of Galois extension.

* `Ideal.card_inertia_eq_ramificationIdxIn`:
  The cardinality of the inertia group is equal to the ramification index.

## References

* [J Neukirch, *Algebraic Number Theory*][Neukirch1992]

-/

open Algebra Module

open scoped Pointwise

attribute [local instance] FractionRing.liftAlgebra

namespace Ideal

open scoped Classical in

noncomputable def ramificationIdxIn {A : Type*} [CommRing A] (p : Ideal A)
    (B : Type*) [CommRing B] [Algebra A B] : ℕ :=
  if h : ∃ P : Ideal B, P.IsPrime ∧ P.LiesOver p then p.ramificationIdx h.choose
  else 0

open scoped Classical in

noncomputable def inertiaDegIn {A : Type*} [CommRing A] (p : Ideal A)
    (B : Type*) [CommRing B] [Algebra A B] : ℕ :=
  if h : ∃ P : Ideal B, P.IsPrime ∧ P.LiesOver p then p.inertiaDeg h.choose else 0

section MulAction

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] {p : Ideal A}
  {G : Type*} [Group G] [MulSemiringAction G B] [SMulCommClass G A B]

-- INSTANCE (free from Core): :
