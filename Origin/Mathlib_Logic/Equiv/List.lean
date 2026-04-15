/-
Extracted from Logic/Equiv/List.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Equivalences involving `List`-like types

This file defines some additional constructive equivalences using `Encodable` and the pairing
function on `ℕ`.
-/

assert_not_exists Monoid Multiset.sort

open List

open Nat

namespace Equiv

def listEquivOfEquiv {α β} (e : α ≃ β) : List α ≃ List β where
  toFun := List.map e
  invFun := List.map e.symm
  left_inv l := by rw [List.map_map, e.symm_comp_self, List.map_id]
  right_inv l := by rw [List.map_map, e.self_comp_symm, List.map_id]

end Equiv

namespace Encodable

variable {α : Type*}

section List

variable [Encodable α]

def encodeList : List α → ℕ
  | [] => 0
  | a :: l => succ (pair (encode a) (encodeList l))

def decodeList : ℕ → Option (List α)
  | 0 => some []
  | succ v =>
    match unpair v, unpair_right_le v with
    | (v₁, v₂), h =>
      have : v₂ < succ v := lt_succ_of_le h
      (· :: ·) <$> decode (α := α) v₁ <*> decodeList v₂
