/-
Extracted from Data/Set/Finite/List.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Finiteness of sets of lists

## Tags

finite sets
-/

assert_not_exists IsOrderedRing MonoidWithZero

namespace List

variable (α : Type*) [Finite α] (n : ℕ)

lemma finite_length_eq : {l : List α | l.length = n}.Finite := List.Vector.finite

lemma finite_length_lt : {l : List α | l.length < n}.Finite := by
  convert (Finset.range n).finite_toSet.biUnion fun i _ ↦ finite_length_eq α i; ext; simp

lemma finite_length_le : {l : List α | l.length ≤ n}.Finite := by
  simpa [Nat.lt_succ_iff] using finite_length_lt α (n + 1)

end List
