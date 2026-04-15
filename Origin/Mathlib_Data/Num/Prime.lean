/-
Extracted from Data/Num/Prime.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Primality for binary natural numbers

This file defines versions of `Nat.minFac` and `Nat.Prime` for `Num` and `PosNum`. As with other
`Num` definitions, they are not intended for general use (`Nat` should be used instead of `Num` in
most cases) but they can be used in contexts where kernel computation is required, such as proofs
by `rfl` and `decide`, as well as in `#reduce`.

The default decidable instance for `Nat.Prime` is optimized for VM evaluation, so it should be
preferred within `#eval` or in tactic execution, while for proofs the `norm_num` tactic can be used
to construct primality and non-primality proofs more efficiently than kernel computation.

Nevertheless, sometimes proof by computational reflection requires natural number computations, and
`Num` implements algorithms directly on binary natural numbers for this purpose.
-/

namespace PosNum

def minFacAux (n : PosNum) : ℕ → PosNum → PosNum
  | 0, _ => n
  | fuel + 1, k =>
    if n < k.bit1 * k.bit1 then n else if k.bit1 ∣ n then k.bit1 else minFacAux n fuel k.succ

theorem minFacAux_to_nat {fuel : ℕ} {n k : PosNum} (h : Nat.sqrt n < fuel + k.bit1) :
    (minFacAux n fuel k : ℕ) = Nat.minFacAux n k.bit1 := by
  induction fuel generalizing k <;> rw [minFacAux, Nat.minFacAux]
  case zero =>
    rw [Nat.zero_add, Nat.sqrt_lt] at h
    simp only [h, ite_true]
  case succ fuel ih =>
    simp_rw [← mul_to_nat]
    simp only [cast_lt, dvd_to_nat]
    split_ifs <;> try rfl
    rw [ih] <;> [congr; convert Nat.lt_succ_of_lt h using 1] <;>
      simp only [cast_bit1, cast_succ, Nat.succ_eq_add_one, add_assoc,
        add_left_comm, ← one_add_one_eq_two]

def minFac : PosNum → PosNum
  | 1 => 1
  | bit0 _ => 2
  | bit1 n => minFacAux (bit1 n) n 1
