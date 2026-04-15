/-
Extracted from RingTheory/Adjoin/Singleton.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Adjoin one single element

This file contains basic results on `Algebra.adjoin`, specifically on adjoining singletons.

## Tags

adjoin, algebra, ringhom

-/

variable {A B C : Type*} [CommSemiring A] [CommSemiring B] [CommSemiring C]

variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] (b : B)

namespace Algebra

open Polynomial

def RingHom.adjoinAlgebraMap :
    A[b] →+* A[(algebraMap B C) b] :=
  RingHom.codRestrict (((Algebra.ofId B C).restrictScalars A).comp
    (Subalgebra.val A[b])) _
    (fun x ↦ by induction x using adjoin_singleton_induction with
      | f p => aesop (add norm [adjoin_singleton_eq_range_aeval, aeval_algebraMap_apply]))
