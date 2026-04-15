/-
Extracted from Data/Finset/BooleanAlgebra.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# `Finset`s are a Boolean algebra

This file provides the `BooleanAlgebra (Finset α)` instance, under the assumption that `α` is a
`Fintype`.

## Main results

* `Finset.boundedOrder`: `Finset.univ` is the top element of `Finset α`
* `Finset.booleanAlgebra`: `Finset α` is a Boolean algebra if `α` is finite
-/

assert_not_exists Monoid

open Function

open Nat

universe u v

variable {α β γ : Type*}

namespace Finset

variable {s t : Finset α}

section Fintypeα

variable [Fintype α]

theorem Nonempty.eq_univ [Subsingleton α] : s.Nonempty → s = univ := by
  rintro ⟨x, hx⟩
  exact eq_univ_of_forall fun y => by rwa [Subsingleton.elim y x]

theorem univ_nonempty_iff : (univ : Finset α).Nonempty ↔ Nonempty α := by
  rw [← coe_nonempty, coe_univ, Set.nonempty_iff_univ_nonempty]
