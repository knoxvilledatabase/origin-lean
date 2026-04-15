/-
Extracted from Analysis/Fourier/FiniteAbelian/PontryaginDuality.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Pontryagin duality for finite abelian groups

This file proves the Pontryagin duality in case of finite abelian groups. This states that any
finite abelian group is canonically isomorphic to its double dual (the space of complex-valued
characters of its space of complex-valued characters).

We first prove it for `ZMod n` and then extend to all finite abelian groups using the
Structure Theorem.

## TODO

Reuse the work done in `Mathlib/GroupTheory/FiniteAbelian/Duality.lean`. This requires to write some
more glue.
-/

noncomputable section

open Circle Finset Function Module Multiplicative

open Fintype (card)

open Real hiding exp

open scoped BigOperators DirectSum

variable {α : Type*} [AddCommGroup α] {n : ℕ} {a b : α}

namespace AddChar

variable (n : ℕ) [NeZero n]

def zmod (x : ZMod n) : AddChar (ZMod n) Circle :=
  AddChar.compAddMonoidHom ⟨AddCircle.toCircle, AddCircle.toCircle_zero, AddCircle.toCircle_add⟩ <|
    ZMod.toAddCircle.comp <| .mulLeft x
