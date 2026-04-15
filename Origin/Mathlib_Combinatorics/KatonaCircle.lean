/-
Extracted from Combinatorics/KatonaCircle.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The Katona circle method

This file provides tooling to use the Katona circle method, which is double-counting ways to order
`n` elements on a circle under some condition.
-/

open Fintype Finset Nat

variable {X : Type*} [Fintype X]

variable (X) in

abbrev Numbering : Type _ := X ≃ Fin (card X)
