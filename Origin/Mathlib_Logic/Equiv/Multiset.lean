/-
Extracted from Logic/Equiv/Multiset.lean
Genuine: 10 of 13 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# `Encodable` and `Denumerable` instances for `Multiset`
-/

variable {α : Type*}

open Encodable

section Finset

variable [Encodable α]

set_option backward.privateInPublic true in

private def enle : α → α → Prop :=
  encode ⁻¹'o (· ≤ ·)

deriving DecidableRel

set_option backward.privateInPublic true in

-- INSTANCE (free from Core): enle.isLinearOrder

set_option backward.privateInPublic true in

set_option backward.privateInPublic.warn false in

def encodeMultiset (s : Multiset α) : ℕ :=
  encode (s.sort enle)

def decodeMultiset (n : ℕ) : Option (Multiset α) :=
  ((↑) : List α → Multiset α) <$> decode (α := List α) n

set_option backward.privateInPublic true in

set_option backward.privateInPublic.warn false in

-- INSTANCE (free from Core): _root_.Multiset.encodable

end Finset

namespace Denumerable

variable [Denumerable α]

section Multiset

def lower : List ℕ → ℕ → List ℕ
  | [], _ => []
  | m :: l, n => (m - n) :: lower l m

def raise : List ℕ → ℕ → List ℕ
  | [], _ => []
  | m :: l, n => (m + n) :: raise l (m + n)

theorem lower_raise : ∀ l n, lower (raise l n) n = l
  | [], _ => rfl
  | m :: l, n => by rw [raise, lower, Nat.add_sub_cancel_right, lower_raise l]

theorem raise_lower : ∀ {l n}, List.SortedLE (n :: l) → raise (lower l n) n = l
  | [], _, _ => rfl
  | m :: l, n, h => by
    have : n ≤ m := List.rel_of_pairwise_cons h.pairwise List.mem_cons_self
    simp [raise, lower, Nat.sub_add_cancel this, raise_lower h.pairwise.of_cons.sortedLE]

theorem isChain_raise : ∀ l n, List.IsChain (· ≤ ·) (raise l n)
  | [], _ => .nil
  | [_], _ => .singleton _
  | _ :: _ :: _, _ => .cons_cons (Nat.le_add_left _ _) (isChain_raise (_ :: _) _)

theorem isChain_cons_raise (l n) : List.IsChain (· ≤ ·) (n :: raise l n) :=
  isChain_raise (n :: l) 0

theorem raise_sorted (l n) : List.SortedLE (raise l n) := (isChain_raise _ _).sortedLE

-- INSTANCE (free from Core): multiset

end Multiset

end Denumerable
