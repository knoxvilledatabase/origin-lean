/-
Extracted from Data/Nat/BitIndices.lean
Genuine: 13 | Conflates: 0 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Bitwise

noncomputable section

/-!
# Bit Indices

Given `n : ℕ`, we define `Nat.bitIndices n`, which is the `List` of indices of `1`s in the
binary expansion of `n`. If `s : Finset ℕ` and `n = ∑ i in s, 2^i`, then
`Nat.bitIndices n` is the sorted list of elements of `s`.

The lemma `twoPowSum_bitIndices` proves that summing `2 ^ i` over this list gives `n`.
This is used in `Combinatorics.colex` to construct a bijection `equivBitIndices : ℕ ≃ Finset ℕ`.

## TODO

Relate the material in this file to `Nat.digits` and `Nat.bits`.
-/

open List

namespace Nat

variable {a n : ℕ}

def bitIndices (n : ℕ) : List ℕ :=
  @binaryRec (fun _ ↦ List ℕ) [] (fun b _ s ↦ b.casesOn (s.map (· + 1)) (0 :: s.map (· + 1))) n

@[simp] theorem bitIndices_zero : bitIndices 0 = [] := by simp [bitIndices]

@[simp] theorem bitIndices_one : bitIndices 1 = [0] := by simp [bitIndices]

theorem bitIndices_bit_true (n : ℕ) :
    bitIndices (bit true n) = 0 :: ((bitIndices n).map (· + 1)) :=
  binaryRec_eq _ _ (.inl rfl)

theorem bitIndices_bit_false (n : ℕ) :
    bitIndices (bit false n) = (bitIndices n).map (· + 1) :=
  binaryRec_eq _ _ (.inl rfl)

@[simp] theorem bitIndices_two_mul_add_one (n : ℕ) :
    bitIndices (2 * n + 1) = 0 :: (bitIndices n).map (· + 1) := by
   rw [← bitIndices_bit_true, bit_true]

@[simp] theorem bitIndices_two_mul (n : ℕ) :
    bitIndices (2 * n) = (bitIndices n).map (· + 1) := by
  rw [← bitIndices_bit_false, bit_false]

@[simp] theorem bitIndices_sorted {n : ℕ} : n.bitIndices.Sorted (· < ·) := by
  induction' n using binaryRec with b n hs
  · simp
  suffices List.Pairwise (fun a b ↦ a < b) n.bitIndices by
    cases b <;> simpa [List.Sorted, bit_false, bit_true, List.pairwise_map]
  exact List.Pairwise.imp (by simp) hs

@[simp] theorem bitIndices_two_pow_mul (k n : ℕ) :
    bitIndices (2^k * n) = (bitIndices n).map (· + k) := by
  induction' k with k ih
  · simp
  rw [add_comm, pow_add, pow_one, mul_assoc, bitIndices_two_mul, ih, List.map_map, comp_add_right]
  simp [add_comm (a := 1)]

@[simp] theorem bitIndices_two_pow (k : ℕ) : bitIndices (2^k) = [k] := by
  rw [← mul_one (a := 2^k), bitIndices_two_pow_mul]; simp

@[simp] theorem twoPowSum_bitIndices (n : ℕ) : (n.bitIndices.map (fun i ↦ 2 ^ i)).sum = n := by
  induction' n using binaryRec with b n hs
  · simp
  have hrw : (fun i ↦ 2^i) ∘ (fun x ↦ x+1) = fun i ↦ 2 * 2 ^ i := by
    ext i; simp [pow_add, mul_comm]
  cases b
  · simpa [hrw, List.sum_map_mul_left]
  simp [hrw, List.sum_map_mul_left, hs, add_comm (a := 1)]

termination_by L.length

theorem two_pow_le_of_mem_bitIndices (ha : a ∈ n.bitIndices) : 2^a ≤ n := by
  rw [← twoPowSum_bitIndices n]
  exact List.single_le_sum (by simp) _ <| mem_map_of_mem _ ha

theorem not_mem_bitIndices_self (n : ℕ) : n ∉ n.bitIndices :=
  fun h ↦ (lt_two_pow n).not_le <| two_pow_le_of_mem_bitIndices h

end Nat
