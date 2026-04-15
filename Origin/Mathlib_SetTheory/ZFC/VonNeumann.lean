/-
Extracted from SetTheory/ZFC/VonNeumann.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Von Neumann hierarchy

This file defines the von Neumann hierarchy of sets `V_ o` for ordinal `o`, which is recursively
defined so that `V_ a = ⋃ b < a, powerset (V_ b)`. This stratifies the universal class, in the sense
that `⋃ o, V_ o = univ`.

## Notation

- `V_ o` is notation for `vonNeumann o`. It is scoped in the `ZFSet` namespace.
-/

universe u

open Order

namespace ZFSet

noncomputable def vonNeumann (o : Ordinal.{u}) : ZFSet.{u} :=
  ⋃ a : Set.Iio o, powerset (vonNeumann a)

termination_by o

decreasing_by exact a.2
