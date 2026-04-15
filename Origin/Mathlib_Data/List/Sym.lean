/-
Extracted from Data/List/Sym.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! # Unordered tuples of elements of a list

Defines `List.sym` and the specialized `List.sym2` for computing lists of all unordered n-tuples
from a given list. These are list versions of `Nat.multichoose`.

## Main declarations

* `List.sym`: `xs.sym n` is a list of all unordered n-tuples of elements from `xs`,
  with multiplicity. The list's values are in `Sym α n`.
* `List.sym2`: `xs.sym2` is a list of all unordered pairs of elements from `xs`,
  with multiplicity. The list's values are in `Sym2 α`.

## TODO

* Prove `protected theorem Perm.sym (n : ℕ) {xs ys : List α} (h : xs ~ ys) : xs.sym n ~ ys.sym n`
  and lift the result to `Multiset` and `Finset`.

-/

namespace List

variable {α β : Type*}

section Sym2

protected def sym2 : List α → List (Sym2 α)
  | [] => []
  | x :: xs => (x :: xs).map (fun y => s(x, y)) ++ xs.sym2

theorem sym2_map (f : α → β) (xs : List α) :
    (xs.map f).sym2 = xs.sym2.map (Sym2.map f) := by
  induction xs with
  | nil => simp [List.sym2]
  | cons x xs ih => simp [List.sym2, ih, Function.comp]

theorem mem_sym2_cons_iff {x : α} {xs : List α} {z : Sym2 α} :
    z ∈ (x :: xs).sym2 ↔ z = s(x, x) ∨ (∃ y, y ∈ xs ∧ z = s(x, y)) ∨ z ∈ xs.sym2 := by
  simp only [List.sym2, map_cons, cons_append, mem_cons, mem_append, mem_map]
  simp only [eq_comm]
