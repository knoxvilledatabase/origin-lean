/-
Extracted from Data/Nat/Upto.lean
Genuine: 5 of 6 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core
import Mathlib.Algebra.Order.Ring.Nat

/-!
# `Nat.Upto`

`Nat.Upto p`, with `p` a predicate on `ℕ`, is a subtype of elements `n : ℕ` such that no value
(strictly) below `n` satisfies `p`.

This type has the property that `>` is well-founded when `∃ i, p i`, which allows us to implement
searches on `ℕ`, starting at `0` and with an unknown upper-bound.

It is similar to the well founded relation constructed to define `Nat.find` with
the difference that, in `Nat.Upto p`, `p` does not need to be decidable. In fact,
`Nat.find` could be slightly altered to factor decidability out of its
well founded relation and would then fulfill the same purpose as this file.
-/

namespace Nat

abbrev Upto (p : ℕ → Prop) : Type :=
  { i : ℕ // ∀ j < i, ¬p j }

namespace Upto

variable {p : ℕ → Prop}

protected def GT (p) (x y : Upto p) : Prop :=
  x.1 > y.1

instance : LT (Upto p) :=
  ⟨fun x y => x.1 < y.1⟩

protected theorem wf : (∃ x, p x) → WellFounded (Upto.GT p)
  | ⟨x, h⟩ => by
    suffices Upto.GT p = InvImage (· < ·) fun y : Nat.Upto p => x - y.val by
      rw [this]
      exact (measure _).wf
    ext ⟨a, ha⟩ ⟨b, _⟩
    dsimp [InvImage, Upto.GT]
    rw [tsub_lt_tsub_iff_left_of_le (le_of_not_lt fun h' => ha _ h' h)]

def zero : Nat.Upto p :=
  ⟨0, fun _ h => False.elim (Nat.not_lt_zero _ h)⟩

def succ (x : Nat.Upto p) (h : ¬p x.val) : Nat.Upto p :=
  ⟨x.val.succ, fun j h' => by
    rcases Nat.lt_succ_iff_lt_or_eq.1 h' with (h' | rfl) <;> [exact x.2 _ h'; exact h]⟩

end Upto

end Nat
