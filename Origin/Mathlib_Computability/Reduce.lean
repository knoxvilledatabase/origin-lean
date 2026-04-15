/-
Extracted from Computability/Reduce.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Strong reducibility and degrees.

This file defines the notions of computable many-one reduction and one-one
reduction between sets, and shows that the corresponding degrees form a
semilattice.

## Notation

This file uses the local notation `⊕'` for `Sum.elim` to denote the disjoint union of two degrees.

## References

* [Robert Soare, *Recursively enumerable sets and degrees*][soare1987]

## Tags

computability, reducibility, reduction
-/

universe u v w

open Function

def ManyOneReducible {α β} [Primcodable α] [Primcodable β] (p : α → Prop) (q : β → Prop) :=
  ∃ f, Computable f ∧ ∀ a, p a ↔ q (f a)
