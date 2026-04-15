/-
Extracted from Algebra/MonoidAlgebra/ToDirectSum.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Conversion between `AddMonoidAlgebra` and homogeneous `DirectSum`

This module provides conversions between `AddMonoidAlgebra` and `DirectSum`.
The latter is essentially a dependent version of the former.

Note that since `DirectSum.instMul` combines indices additively, there is no equivalent to
`MonoidAlgebra`.

## Main definitions

* `AddMonoidAlgebra.toDirectSum : AddMonoidAlgebra M ι → (⨁ i : ι, M)`
* `DirectSum.toAddMonoidAlgebra : (⨁ i : ι, M) → AddMonoidAlgebra M ι`
* Bundled equiv versions of the above:
  * `addMonoidAlgebraEquivDirectSum : AddMonoidAlgebra M ι ≃ (⨁ i : ι, M)`
  * `addMonoidAlgebraAddEquivDirectSum : AddMonoidAlgebra M ι ≃+ (⨁ i : ι, M)`
  * `addMonoidAlgebraRingEquivDirectSum R : AddMonoidAlgebra M ι ≃+* (⨁ i : ι, M)`
  * `addMonoidAlgebraAlgEquivDirectSum R : AddMonoidAlgebra A ι ≃ₐ[R] (⨁ i : ι, A)`

## Theorems

The defining feature of these operations is that they map `AddMonoidAlgebra.single` to
`DirectSum.of` and vice versa:

* `AddMonoidAlgebra.toDirectSum_single`
* `DirectSum.toAddMonoidAlgebra_of`

as well as preserving arithmetic operations.

For the bundled equivalences, we provide lemmas that they reduce to
`AddMonoidAlgebra.toDirectSum`:

* `addMonoidAlgebraAddEquivDirectSum_apply`
* `add_monoid_algebra_lequiv_direct_sum_apply`
* `addMonoidAlgebraAddEquivDirectSum_symm_apply`
* `add_monoid_algebra_lequiv_direct_sum_symm_apply`

## Implementation notes

This file largely just copies the API of `Mathlib/Data/Finsupp/ToDFinsupp.lean`, and reuses the
proofs. Recall that `AddMonoidAlgebra M ι` is defeq to `ι →₀ M` and `⨁ i : ι, M` is defeq to
`Π₀ i : ι, M`.
-/

variable {ι : Type*} {R : Type*} {M : Type*} {A : Type*}

open DirectSum

/-! ### Basic definitions and lemmas -/

section Defs

def AddMonoidAlgebra.toDirectSum [Semiring M] (f : AddMonoidAlgebra M ι) : ⨁ _ : ι, M :=
  Finsupp.toDFinsupp f

variable [DecidableEq ι] [Semiring M]
