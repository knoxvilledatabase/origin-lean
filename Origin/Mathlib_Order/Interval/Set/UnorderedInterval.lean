/-
Extracted from Order/Interval/Set/UnorderedInterval.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Intervals without endpoints ordering

In any lattice `α`, we define `uIcc a b` to be `Icc (a ⊓ b) (a ⊔ b)`, which in a linear order is
the set of elements lying between `a` and `b`.

`Icc a b` requires the assumption `a ≤ b` to be meaningful, which is sometimes inconvenient. The
interval as defined in this file is always the set of things lying between `a` and `b`, regardless
of the relative order of `a` and `b`.

For real numbers, `uIcc a b` is the same as `segment ℝ a b`.

In a product or pi type, `uIcc a b` is the smallest box containing `a` and `b`. For example,
`uIcc (1, -1) (-1, 1) = Icc (-1, -1) (1, 1)` is the square of vertices `(1, -1)`, `(-1, -1)`,
`(-1, 1)`, `(1, 1)`.

In `Finset α` (seen as a hypercube of dimension `Fintype.card α`), `uIcc a b` is the smallest
subcube containing both `a` and `b`.

## Notation

We use the localized notation `[[a, b]]` for `uIcc a b`. One can open the scope `Interval` to
make the notation available.

-/

open Function

open OrderDual (toDual ofDual)

variable {α β : Type*}

namespace Set

section Lattice

variable [Lattice α] [Lattice β] {a a₁ a₂ b b₁ b₂ x : α}

def uIcc (a b : α) : Set α := Icc (a ⊓ b) (a ⊔ b)

scoped[Interval] notation "[[" a ", " b "]]" => Set.uIcc a b

open Interval
