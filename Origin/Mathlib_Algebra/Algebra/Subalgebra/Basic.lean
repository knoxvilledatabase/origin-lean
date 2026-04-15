/-
Extracted from Algebra/Algebra/Subalgebra/Basic.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Subalgebras over Commutative Semiring

In this file we define `Subalgebra`s and the usual operations on them (`map`, `comap`).

The `Algebra.adjoin` operation and complete lattice structure can be found in
`Mathlib/Algebra/Algebra/Subalgebra/Lattice.lean`.
-/

open Module

universe u u' v w w'

structure Subalgebra (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] [Algebra R A] : Type v
    extends Subsemiring A where
  /-- The image of `algebraMap` is contained in the underlying set of the subalgebra -/
  algebraMap_mem' : ∀ r, algebraMap R A r ∈ carrier
  zero_mem' := (algebraMap R A).map_zero ▸ algebraMap_mem' 0
  one_mem' := (algebraMap R A).map_one ▸ algebraMap_mem' 1

add_decl_doc Subalgebra.toSubsemiring

namespace Subalgebra

variable {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

initialize_simps_projections Subalgebra (carrier → coe, as_prefix coe)
