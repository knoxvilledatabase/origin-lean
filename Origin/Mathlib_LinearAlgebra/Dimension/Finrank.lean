/-
Extracted from LinearAlgebra/Dimension/Finrank.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Finite dimension of vector spaces

Definition of the rank of a module, or dimension of a vector space, as a natural number.

## Main definitions

Defined is `Module.finrank`, the dimension of a finite-dimensional space, returning a
`Nat`, as opposed to `Module.rank`, which returns a `Cardinal`. When the space has infinite
dimension, its `finrank` is by convention set to `0`.

The definition of `finrank` does not assume a `FiniteDimensional` instance, but lemmas might.
Import `LinearAlgebra.FiniteDimensional` to get access to these additional lemmas.

Formulas for the dimension are given for linear equivs, in `LinearEquiv.finrank_eq`.

## Implementation notes

Most results are deduced from the corresponding results for the general dimension (as a cardinal),
in `Dimension.lean`. Not all results have been ported yet.

You should not assume that there has been any effort to state lemmas as generally as possible.
-/

universe u v w

open Cardinal Submodule Module Function

variable {R : Type u} {M : Type v} {N : Type w}

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

namespace Module

section Semiring

noncomputable def finrank (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M] : ℕ :=
  Cardinal.toNat (Module.rank R M)
