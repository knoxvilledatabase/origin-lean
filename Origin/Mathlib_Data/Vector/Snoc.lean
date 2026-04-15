/-
Extracted from Data/Vector/Snoc.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
  This file establishes a `snoc : Vector α n → α → Vector α (n+1)` operation, that appends a single
  element to the back of a vector.

  It provides a collection of lemmas that show how different `Vector` operations reduce when their
  argument is `snoc xs x`.

  Also, an alternative, reverse, induction principle is added, that breaks down a vector into
  `snoc xs x` for its inductive case. Effectively doing induction from right-to-left
-/

namespace List

namespace Vector

variable {α β σ φ : Type*} {n : ℕ} {x : α} {s : σ} (xs : Vector α n)

def snoc : Vector α n → α → Vector α (n + 1) :=
  fun xs x => xs ++ x ::ᵥ Vector.nil

/-! ## Simplification lemmas -/

section Simp

variable {y : α}
