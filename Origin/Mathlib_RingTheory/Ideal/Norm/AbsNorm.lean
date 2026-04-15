/-
Extracted from RingTheory/Ideal/Norm/AbsNorm.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!

# Ideal norms

This file defines the absolute ideal norm `Ideal.absNorm (I : Ideal R) : ℕ` as the cardinality of
the quotient `R ⧸ I` (setting it to 0 if the cardinality is infinite).

## Main definitions

* `Submodule.cardQuot (S : Submodule R M)`: the cardinality of the quotient `M ⧸ S`, in `ℕ`.
  This maps `⊥` to `0` and `⊤` to `1`.
* `Ideal.absNorm (I : Ideal R)`: the absolute ideal norm, defined as
  the cardinality of the quotient `R ⧸ I`, as a bundled monoid-with-zero homomorphism.

## Main results

* `map_mul Ideal.absNorm`: multiplicativity of the ideal norm is bundled in
  the definition of `Ideal.absNorm`
* `Ideal.natAbs_det_basis_change`: the ideal norm is given by the determinant
  of the basis change matrix
* `Ideal.absNorm_span_singleton`: the ideal norm of a principal ideal is the
  norm of its generator
-/

open Module

open scoped nonZeroDivisors

section abs_norm

namespace Submodule

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

noncomputable def cardQuot (S : Submodule R M) : ℕ :=
  AddSubgroup.index S.toAddSubgroup

variable (R M)
