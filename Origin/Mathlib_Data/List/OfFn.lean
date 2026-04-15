/-
Extracted from Data/List/OfFn.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Lists from functions

Theorems and lemmas for dealing with `List.ofFn`, which converts a function on `Fin n` to a list
of length `n`.

## Main Statements

The main statements pertain to lists generated using `List.ofFn`

- `List.get?_ofFn`, which tells us the nth element of such a list
- `List.equivSigmaTuple`, which is an `Equiv` between lists and the functions that generate them
  via `List.ofFn`.
-/

assert_not_exists Monoid

universe u

variable {α : Type u}

open Nat

namespace List

theorem get_ofFn {n} (f : Fin n → α) (i) : get (ofFn f) i = f (Fin.cast (by simp) i) := by
  simp; congr

theorem ofFn_comp' {β : Type*} {n : ℕ} (f : Fin n → α) (g : α → β) :
    ofFn (fun i => g (f i)) = map g (ofFn f) :=
  map_ofFn.symm
