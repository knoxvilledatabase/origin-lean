/-
Extracted from LinearAlgebra/CliffordAlgebra/Conjugation.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Conjugations

This file defines the grade reversal and grade involution functions on multivectors, `reverse` and
`involute`.
Together, these operations compose to form the "Clifford conjugate", hence the name of this file.

https://en.wikipedia.org/wiki/Clifford_algebra#Antiautomorphisms

## Main definitions

* `CliffordAlgebra.involute`: the grade involution, negating each basis vector
* `CliffordAlgebra.reverse`: the grade reversion, reversing the order of a product of vectors

## Main statements

* `CliffordAlgebra.involute_involutive`
* `CliffordAlgebra.reverse_involutive`
* `CliffordAlgebra.reverse_involute_commute`
* `CliffordAlgebra.involute_mem_evenOdd_iff`
* `CliffordAlgebra.reverse_mem_evenOdd_iff`

-/

variable {R : Type*} [CommRing R]

variable {M : Type*} [AddCommGroup M] [Module R M]

variable {Q : QuadraticForm R M}

namespace CliffordAlgebra

section Involute

def involute : CliffordAlgebra Q →ₐ[R] CliffordAlgebra Q :=
  CliffordAlgebra.lift Q ⟨-ι Q, fun m => by simp⟩
