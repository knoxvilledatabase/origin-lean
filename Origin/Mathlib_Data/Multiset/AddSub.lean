/-
Extracted from Data/Multiset/AddSub.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Sum and difference of multisets

This file defines the following operations on multisets:

* `Add (Multiset α)` instance: `s + t` adds the multiplicities of the elements of `s` and `t`
* `Sub (Multiset α)` instance: `s - t` subtracts the multiplicities of the elements of `s` and `t`
* `Multiset.erase`: `s.erase x` reduces the multiplicity of `x` in `s` by one.

## Notation (defined later)

* `s + t`: The multiset for which the number of occurrences of each `a` is the sum of the
  occurrences of `a` in `s` and `t`.
* `s - t`: The multiset for which the number of occurrences of each `a` is the difference of the
  occurrences of `a` in `s` and `t`.

-/

assert_not_exists Monoid

universe v

open List Subtype Nat Function

variable {α : Type*} {β : Type v} {γ : Type*}

namespace Multiset

/-! ### Additive monoid -/

section add

variable {s t u : Multiset α}

protected def add (s₁ s₂ : Multiset α) : Multiset α :=
  (Quotient.liftOn₂ s₁ s₂ fun l₁ l₂ => ((l₁ ++ l₂ : List α) : Multiset α)) fun _ _ _ _ p₁ p₂ =>
    Quot.sound <| p₁.append p₂

-- INSTANCE (free from Core): :
