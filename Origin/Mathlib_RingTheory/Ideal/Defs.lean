/-
Extracted from RingTheory/Ideal/Defs.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Ideals over a ring

This file defines `Ideal R`, the type of (left) ideals over a ring `R`.
Note that over commutative rings, left ideals and two-sided ideals are equivalent.

## Implementation notes

`Ideal R` is implemented using `Submodule R R`, where `•` is interpreted as `*`.

## TODO

Support right ideals, and two-sided ideals over non-commutative rings.
-/

universe u v w

variable {α : Type u} {β : Type v} {F : Type w}

open Set Function

open Pointwise

abbrev Ideal (R : Type u) [Semiring R] :=
  Submodule R R

section Semiring

namespace Ideal

variable [Semiring α] (I : Ideal α) {a b : α}
