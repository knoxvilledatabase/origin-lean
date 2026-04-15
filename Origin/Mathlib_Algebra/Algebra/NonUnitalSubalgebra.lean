/-
Extracted from Algebra/Algebra/NonUnitalSubalgebra.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Non-unital Subalgebras over Commutative Semirings

In this file we define `NonUnitalSubalgebra`s and the usual operations on them (`map`, `comap`).

## TODO

* once we have scalar actions by semigroups (as opposed to monoids), implement the action of a
  non-unital subalgebra on the larger algebra.
-/

universe u u' v v' w w'

section NonUnitalSubalgebraClass

variable {S R A : Type*} [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]

variable [SetLike S A] [NonUnitalSubsemiringClass S A] [hSR : SMulMemClass S R A] (s : S)

namespace NonUnitalSubalgebraClass

def subtype (s : S) : s →ₙₐ[R] A :=
  { NonUnitalSubsemiringClass.subtype s, SMulMemClass.subtype s with toFun := (↑) }

variable {s} in
