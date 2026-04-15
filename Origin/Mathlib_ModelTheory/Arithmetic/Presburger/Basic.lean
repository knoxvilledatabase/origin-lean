/-
Extracted from ModelTheory/Arithmetic/Presburger/Basic.lean
Genuine: 2 of 6 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# Presburger arithmetic

This file defines the first-order language of Presburger arithmetic as (0,1,+).

## Main Definitions

- `FirstOrder.Language.presburger`: the language of Presburger arithmetic.

## TODO

- Generalize `presburger.sum` (maybe also `NatCast` and `SMul`) for classes like
  `FirstOrder.Language.IsOrdered`.
- Define the theory of Presburger arithmetic and prove its properties (quantifier elimination,
  completeness, etc).
-/

variable {α : Type*}

namespace FirstOrder

inductive presburgerFunc : ℕ → Type
  | zero : presburgerFunc 0
  | one : presburgerFunc 0
  | add : presburgerFunc 2
  deriving DecidableEq

def Language.presburger : Language :=
  { Functions := presburgerFunc
    Relations := fun _ => Empty }
  deriving IsAlgebraic

namespace Language.presburger

variable {t t₁ t₂ : presburger.Term α}

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :
