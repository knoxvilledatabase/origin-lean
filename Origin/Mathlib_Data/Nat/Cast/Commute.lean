/-
Extracted from Data/Nat/Cast/Commute.lean
Genuine: 5 of 5 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Cast of natural numbers: lemmas about `Commute`

-/

variable {α : Type*}

namespace Nat

section Commute

variable [NonAssocSemiring α]

theorem cast_commute (n : ℕ) (x : α) : Commute (n : α) x := by
  induction n with
  | zero => rw [Nat.cast_zero]; exact Commute.zero_left x
  | succ n ihn => rw [Nat.cast_succ]; exact ihn.add_left (Commute.one_left x)

theorem _root_.Commute.ofNat_left (n : ℕ) [n.AtLeastTwo] (x : α) : Commute (OfNat.ofNat n) x :=
  n.cast_commute x

theorem cast_comm (n : ℕ) (x : α) : (n : α) * x = x * n :=
  (cast_commute n x).eq

theorem commute_cast (x : α) (n : ℕ) : Commute x n :=
  (n.cast_commute x).symm

theorem _root_.Commute.ofNat_right (x : α) (n : ℕ) [n.AtLeastTwo] : Commute x (OfNat.ofNat n) :=
  n.commute_cast x

end Commute

end Nat

namespace SemiconjBy

variable [Semiring α] {a x y : α}
