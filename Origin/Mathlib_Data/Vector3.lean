/-
Extracted from Data/Vector3.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Alternate definition of `Vector` in terms of `Fin2`

This file provides a scope `Vector3` which overrides the `[a, b, c]` notation to create a `Vector3`
instead of a `List`.

The `::` notation is also overloaded by this file to mean `Vector3.cons`.
-/

open Fin2 Nat

universe u

variable {α : Type*} {m n : ℕ}

def Vector3 (α : Type u) (n : ℕ) : Type u :=
  Fin2 n → α

-- INSTANCE (free from Core): [Inhabited

namespace Vector3
