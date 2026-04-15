/-
Extracted from Data/List/Defs.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
## Definitions on lists

This file contains various definitions on lists. It does not contain
proofs about these definitions, those are contained in other files in `Data.List`
-/

namespace List

open Function Nat

universe u v w x

variable {α β γ δ ε ζ : Type*}

-- INSTANCE (free from Core): [DecidableEq

def getI [Inhabited α] (l : List α) (n : Nat) : α :=
  getD l n default

def headI [Inhabited α] : List α → α
  | [] => default
  | (a :: _) => a
