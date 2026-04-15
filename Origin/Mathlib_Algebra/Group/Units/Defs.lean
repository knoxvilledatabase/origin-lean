/-
Extracted from Algebra/Group/Units/Defs.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Units (i.e., invertible elements) of a monoid

An element of a `Monoid` is a unit if it has a two-sided inverse.

## Main declarations

* `Units M`: the group of units (i.e., invertible elements) of a monoid.
* `IsUnit x`: a predicate asserting that `x` is a unit (i.e., invertible element) of a monoid.

For both declarations, there is an additive counterpart: `AddUnits` and `IsAddUnit`.
See also `Prime`, `Associated`, and `Irreducible` in
`Mathlib/Algebra/GroupWithZero/Associated.lean`.

## Notation

We provide `Mˣ` as notation for `Units M`,
resembling the notation $R^{\times}$ for the units of a ring, which is common in mathematics.

## TODO

The results here should be used to golf the basic `Group` lemmas.
-/

assert_not_exists Multiplicative MonoidWithZero DenselyOrdered

open Function

universe u

variable {α : Type u}

structure Units (α : Type u) [Monoid α] where
  /-- The underlying value in the base `Monoid`. -/
  val : α
  /-- The inverse value of `val` in the base `Monoid`. -/
  inv : α
  /-- `inv` is the right inverse of `val` in the base `Monoid`. -/
  val_inv : val * inv = 1
  /-- `inv` is the left inverse of `val` in the base `Monoid`. -/
  inv_val : inv * val = 1

attribute [coe] Units.val
