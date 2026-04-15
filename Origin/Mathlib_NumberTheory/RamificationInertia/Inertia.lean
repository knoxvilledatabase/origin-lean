/-
Extracted from NumberTheory/RamificationInertia/Inertia.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Ramification index and inertia degree

Given `P : Ideal S` lying over `p : Ideal R` for the ring extension `f : R →+* S`
(assuming `P` and `p` are prime or maximal where needed),
the **inertia degree** `Ideal.inertiaDeg p P` is the degree of the field extension
`(S / P) : (R / p)`.

## Implementation notes

Often the above theory is set up in the case where:
* `R` is the ring of integers of a number field `K`,
* `L` is a finite separable extension of `K`,
* `S` is the integral closure of `R` in `L`,
* `p` and `P` are maximal ideals,
* `P` is an ideal lying over `p`

We will try to relax the above hypotheses as much as possible.

## Notation

In this file, `f` stands for the inertia degree of `P` over `p`, leaving `p` and `P` implicit.

-/

namespace Ideal

universe u v

variable {R : Type u} [CommRing R]

variable {S : Type v} [CommRing S] [Algebra R S]

variable (p : Ideal R) (P : Ideal S)

local notation "f" => algebraMap R S

open Module

open UniqueFactorizationMonoid

attribute [local instance] Ideal.Quotient.field

section DecEq

variable {S₁ : Type*} [CommRing S₁] [Algebra R S₁]

open Classical in

noncomputable def inertiaDeg : ℕ :=
  if hPp : comap f P = p then
    letI : Algebra (R ⧸ p) (S ⧸ P) := Quotient.algebraQuotientOfLEComap hPp.ge
    finrank (R ⧸ p) (S ⧸ P)
  else 0
