/-
Extracted from RingTheory/Jacobson/Ideal.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Jacobson radical

The Jacobson radical of a ring `R` is defined to be the intersection of all maximal ideals of `R`.
This is similar to how the nilradical is equal to the intersection of all prime ideals of `R`.

We can extend the idea of the nilradical of `R` to ideals of `R`,
by letting the nilradical of an ideal `I` be the intersection of prime ideals containing `I`.
Under this extension, the original nilradical is the radical of the zero ideal `⊥`.
Here we define the Jacobson radical of an ideal `I` in a similar way,
as the intersection of maximal ideals containing `I`.

## Main definitions

Let `R` be a ring, and `I` be a left ideal of `R`

* `Ideal.jacobson I` is the Jacobson radical, i.e. the infimum of all maximal ideals containing `I`.

* `Ideal.IsLocal I` is the proposition that the Jacobson radical of `I` is itself a maximal ideal

Furthermore when `I` is a two-sided ideal of `R`

* `TwoSidedIdeal.jacobson I` is the Jacobson radical as a two-sided ideal

## Main statements

* `mem_jacobson_iff` gives a characterization of members of the Jacobson of I

* `Ideal.isLocal_of_isMaximal_radical`: if the radical of I is maximal then so is the Jacobson
  radical

## Tags

Jacobson, Jacobson radical, Local Ideal

-/

universe u v

namespace Ideal

variable {R : Type u} {S : Type v}

section Jacobson

section Ring

variable [Ring R] [Ring S] {I : Ideal R}

def jacobson (I : Ideal R) : Ideal R :=
  sInf { J : Ideal R | I ≤ J ∧ IsMaximal J }

theorem le_jacobson : I ≤ jacobson I := fun _ hx => mem_sInf.mpr fun _ hJ => hJ.left hx
