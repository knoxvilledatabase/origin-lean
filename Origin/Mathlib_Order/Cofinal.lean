/-
Extracted from Order/Cofinal.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Cofinal sets

A set `s` in an ordered type `α` is cofinal when for every `a : α` there exists an element of `s`
greater or equal to it. This file provides a basic API for the `IsCofinal` predicate.

For the cofinality of a set as a cardinal, see `Mathlib/SetTheory/Cardinal/Cofinality.lean`.

## TODO

- Define `Order.cof` in terms of `Cofinal`.
- Deprecate `Order.Cofinal` in favor of this predicate.
-/

open Set

variable {α β : Type*}

section LE

variable [LE α]

theorem IsCofinal.of_isEmpty [IsEmpty α] (s : Set α) : IsCofinal s :=
  fun a ↦ isEmptyElim a

theorem isCofinal_empty_iff : IsCofinal (∅ : Set α) ↔ IsEmpty α := by
  refine ⟨fun h ↦ ⟨fun a ↦ ?_⟩, fun h ↦ .of_isEmpty _⟩
  simpa using h a
