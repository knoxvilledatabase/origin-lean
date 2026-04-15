/-
Extracted from Algebra/BigOperators/Ring/List.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Big operators on a list in rings

This file contains the results concerning the interaction of list big operators with rings.
-/

open MulOpposite List

variable {ι κ M M₀ R : Type*}

namespace Commute

variable [NonUnitalNonAssocSemiring R]

lemma list_sum_right (a : R) (l : List R) (h : ∀ b ∈ l, Commute a b) : Commute a l.sum := by
  induction l with
  | nil => exact Commute.zero_right _
  | cons x xs ih =>
    rw [List.sum_cons]
    exact (h _ mem_cons_self).add_right (ih fun j hj ↦ h _ <| mem_cons_of_mem _ hj)

lemma list_sum_left (b : R) (l : List R) (h : ∀ a ∈ l, Commute a b) : Commute l.sum b :=
  ((Commute.list_sum_right _ _) fun _x hx ↦ (h _ hx).symm).symm

end Commute

namespace List

section HasDistribNeg

variable [Monoid M] [HasDistribNeg M]
