/-
Extracted from Data/Bracket.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Tactic.TypeStar

/-!
# Bracket Notation
This file provides notation which can be used for the Lie bracket, for the commutator of two
subgroups, and for other similar operations.

## Main Definitions

* `Bracket L M` for a binary operation that takes something in `L` and something in `M` and
produces something in `M`. Defining an instance of this structure gives access to the notation `⁅ ⁆`

## Notation

We introduce the notation `⁅x, y⁆` for the `bracket` of any `Bracket` structure. Note that
these are the Unicode "square with quill" brackets rather than the usual square brackets.
-/

class Bracket (L M : Type*) where
  /-- `⁅x, y⁆` is the result of a bracket operation on elements `x` and `y`.
  It is supported by the `Bracket` typeclass. -/
  bracket : L → M → M
