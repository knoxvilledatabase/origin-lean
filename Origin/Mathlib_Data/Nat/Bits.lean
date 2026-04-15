/-
Extracted from Data/Nat/Bits.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Additional properties of binary recursion on `Nat`

This file documents additional properties of binary recursion,
which allows us to more easily work with operations which do depend
on the number of leading zeros in the binary representation of `n`.
For example, we can more easily work with `Nat.bits` and `Nat.size`.

See also: `Nat.bitwise`, `Nat.pow` (for various lemmas about `size` and `shiftLeft`/`shiftRight`),
and `Nat.digits`.
-/

assert_not_exists Monoid

local notation "bxor" => xor

namespace Nat

universe u

variable {m n : ℕ}

def boddDiv2 : ℕ → Bool × ℕ
  | 0 => (false, 0)
  | succ n =>
    match boddDiv2 n with
    | (false, m) => (true, m)
    | (true, m) => (false, succ m)

def div2 (n : ℕ) : ℕ := (boddDiv2 n).2

def bodd (n : ℕ) : Bool := (boddDiv2 n).1
