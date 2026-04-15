/-
Extracted from Data/SProd.lean
Genuine: 1 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Tactic.FBinop

/-!
# Set Product Notation
This file provides notation for a product of sets, and other similar types.

## Main Definitions

* `SProd α β γ` for a binary operation `(· ×ˢ ·) : α → β → γ`.

## Notation

We introduce the notation `x ×ˢ y` for the `sprod` of any `SProd` structure. Ideally, `x × y`
notation is desirable but this notation is defined in core for `Prod` so replacing `x ×ˢ y` with
`x × y` seems difficult.
-/

universe u v w

class SProd (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /-- The cartesian product `s ×ˢ t` is the set of `(a, b)` such that `a ∈ s` and `b ∈ t`. -/
  sprod : α → β → γ

macro_rules | `($x ×ˢ $y)   => `(fbinop% SProd.sprod $x $y)
