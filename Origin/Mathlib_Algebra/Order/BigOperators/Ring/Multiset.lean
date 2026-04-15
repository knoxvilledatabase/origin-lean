/-
Extracted from Algebra/Order/BigOperators/Ring/Multiset.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Algebra.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.BigOperators.Ring.List

/-!
# Big operators on a multiset in ordered rings

This file contains the results concerning the interaction of multiset big operators with ordered
rings.
-/

@[simp]
lemma CanonicallyOrderedCommSemiring.multiset_prod_pos {R : Type*}
    [CanonicallyOrderedCommSemiring R] [Nontrivial R] {m : Multiset R} :
    0 < m.prod ↔ ∀ x ∈ m, 0 < x := by
  rcases m with ⟨l⟩
  rw [Multiset.quot_mk_to_coe'', Multiset.prod_coe]
  exact CanonicallyOrderedCommSemiring.list_prod_pos
