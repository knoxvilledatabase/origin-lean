/-
Extracted from SetTheory/Cardinal/Finite.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Finite Cardinality Functions

## Main Definitions

* `Nat.card α` is the cardinality of `α` as a natural number.
  If `α` is infinite, `Nat.card α = 0`.
* `ENat.card α` is the cardinality of `α` as an extended natural number.
  If `α` is infinite, `ENat.card α = ⊤`.
-/

assert_not_exists Field

open Cardinal Function

noncomputable section

variable {α β : Type*}

universe u v

namespace Nat

protected def card (α : Type*) : ℕ :=
  toNat (mk α)
