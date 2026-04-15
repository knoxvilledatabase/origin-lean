/-
Extracted from LinearAlgebra/TensorPower/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Tensor power of a semimodule over a commutative semiring

We define the `n`th tensor power of `M` as the n-ary tensor product indexed by `Fin n` of `M`,
`⨂[R] (i : Fin n), M`. This is a special case of `PiTensorProduct`.

This file introduces the notation `⨂[R]^n M` for `TensorPower R n M`, which in turn is an
abbreviation for `⨂[R] i : Fin n, M`.

## Main definitions:

* `TensorPower.gsemiring`: the tensor powers form a graded semiring.
* `TensorPower.galgebra`: the tensor powers form a graded algebra.

## Implementation notes

In this file we use `ₜ1` and `ₜ*` as local notation for the graded multiplicative structure on
tensor powers. Elsewhere, using `1` and `*` on `GradedMonoid` should be preferred.
-/

open scoped TensorProduct

abbrev TensorPower (R : Type*) (n : ℕ) (M : Type*) [CommSemiring R] [AddCommMonoid M]
    [Module R M] : Type _ :=
  ⨂[R] _ : Fin n, M

variable {R : Type*} {M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
