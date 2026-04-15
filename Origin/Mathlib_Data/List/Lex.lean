/-
Extracted from Data/List/Lex.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Lexicographic ordering of lists.

The lexicographic order on `List α` is defined by `L < M` iff
* `[] < (a :: L)` for any `a` and `L`,
* `(a :: L) < (b :: M)` where `a < b`, or
* `(a :: L) < (a :: M)` where `L < M`.

## See also

Related files are:
* `Mathlib/Combinatorics/Colex.lean`: Colexicographic order on finite sets.
* `Mathlib/Data/PSigma/Order.lean`: Lexicographic order on `Σ' i, α i`.
* `Mathlib/Order/PiLex.lean`: Lexicographic order on `Πₗ i, α i`.
* `Mathlib/Data/Sigma/Order.lean`: Lexicographic order on `Σ i, α i`.
* `Mathlib/Data/Prod/Lex.lean`: Lexicographic order on `α × β`.
-/

namespace List

open Nat

universe u

variable {α : Type u}

/-! ### lexicographic ordering -/

theorem lex_nil_or_eq_nil {r : α → α → Prop} (l : List α) : List.Lex r [] l ∨ l = [] :=
  match l with
  | [] => Or.inr rfl
  | _ :: _ => .inl .nil
