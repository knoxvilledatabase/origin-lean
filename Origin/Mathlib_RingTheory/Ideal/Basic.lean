/-
Extracted from RingTheory/Ideal/Basic.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!

# Ideals over a ring

This file contains an assortment of definitions and results for `Ideal R`,
the type of (left) ideals over a ring `R`.
Note that over commutative rings, left ideals and two-sided ideals are equivalent.

## Implementation notes

`Ideal R` is implemented using `Submodule R R`, where `•` is interpreted as `*`.

## TODO

Support right ideals, and two-sided ideals over non-commutative rings.
-/

variable {ι α β F : Type*}

open Set Function

open Pointwise

section Semiring

namespace Ideal

variable {R : ι → Type*} [Π i, Semiring (R i)] (I J : Π i, Ideal (R i))

section Pi

def pi : Ideal (Π i, R i) where
  carrier := { r | ∀ i, r i ∈ I i }
  zero_mem' i := (I i).zero_mem
  add_mem' ha hb i := (I i).add_mem (ha i) (hb i)
  smul_mem' a _b hb i := (I i).mul_mem_left (a i) (hb i)
