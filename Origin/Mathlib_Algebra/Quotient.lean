/-
Extracted from Algebra/Quotient.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Algebraic quotients

This file defines notation for algebraic quotients, e.g. quotient groups `G ⧸ H`,
quotient modules `M ⧸ N` and ideal quotients `R ⧸ I`.

The actual quotient structures are defined in the following files:
* Quotient Group: `Mathlib/GroupTheory/QuotientGroup/Defs.lean`
* Quotient Module: `Mathlib/LinearAlgebra/Quotient/Defs.lean`
* Quotient Ring: `Mathlib/RingTheory/Ideal/Quotient/Defs.lean`

## Notation

The following notation is introduced:

* `G ⧸ H` stands for the quotient of the type `G` by some term `H`
  (for example, `H` can be a normal subgroup of `G`).
  To implement this notation for other quotients, you should provide a `HasQuotient` instance.
  Note that since `G` can usually be inferred from `H`, `_ ⧸ H` can also be used,
  but this is less readable.

## Tags

quotient, group quotient, quotient group, module quotient, quotient module, ring quotient,
ideal quotient, quotient ring
-/

universe u v

class HasQuotient (A : outParam <| Type u) (B : Type v) where
  /-- `HasQuotient.Quotient A b` (denoted as `A ⧸ b`) is the quotient of the type `A` by `b`. -/
  Quotient (A) : B → Type max u v
