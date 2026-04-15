/-
Extracted from Data/W/Constructions.lean
Genuine: 2 of 4 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Examples of W-types

We take the view of W types as inductive types.
Given `α : Type` and `β : α → Type`, the W type determined by this data, `WType β`, is the
inductively with constructors from `α` and arities of each constructor `a : α` given by `β a`.

This file contains `Nat` and `List` as examples of W types.

## Main results
* `WType.equivNat`: the construction of the naturals as a W-type is equivalent to `Nat`
* `WType.equivList`: the construction of lists on a type `γ` as a W-type is equivalent to `List γ`
-/

universe u v

namespace WType

section Nat

inductive Natα : Type
  | zero : Natα
  | succ : Natα

-- INSTANCE (free from Core): :

def Natβ : Natα → Type
  | Natα.zero => Empty
  | Natα.succ => Unit

-- INSTANCE (free from Core): :
