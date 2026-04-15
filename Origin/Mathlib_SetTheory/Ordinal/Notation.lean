/-
Extracted from SetTheory/Ordinal/Notation.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Ordinal notation

Constructive ordinal arithmetic for ordinals below `ε₀`.

We define a type `ONote`, with constructors `0 : ONote` and `ONote.oadd e n a` representing
`ω ^ e * n + a`.
We say that `o` is in Cantor normal form - `ONote.NF o` - if either `o = 0` or
`o = ω ^ e * n + a` with `a < ω ^ e` and `a` in Cantor normal form.

The type `NONote` is the type of ordinals below `ε₀` in Cantor normal form.
Various operations (addition, subtraction, multiplication, exponentiation)
are defined on `ONote` and `NONote`.
-/

open Ordinal Order

set_option genSizeOfSpec false in

inductive ONote : Type
  | zero : ONote
  | oadd : ONote → ℕ+ → ONote → ONote
  deriving DecidableEq

compile_inductive% ONote

namespace ONote

-- INSTANCE (free from Core): :
