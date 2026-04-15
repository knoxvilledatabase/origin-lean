/-
Extracted from Data/Nat/Init.lean
Genuine: 7 of 16 | Dissolved: 2 | Infrastructure: 7
-/
import Origin.Core

/-!
# Basic operations on the natural numbers

This file contains:
* some basic lemmas about natural numbers
* extra recursors:
  * `leRecOn`, `le_induction`: recursion and induction principles starting at non-zero numbers
  * `decreasing_induction`: recursion growing downwards
  * `le_rec_on'`, `decreasing_induction'`: versions with slightly weaker assumptions
  * `strong_rec'`: recursion based on strong inequalities
* decidability instances on predicates about the natural numbers

This file should not depend on anything defined in Mathlib (except for notation), so that it can be
upstreamed to Batteries or the Lean standard library easily.

See note [foundational algebra order theory].
-/

library_note «foundational algebra order theory» /--

Batteries has a home-baked development of the algebraic and order-theoretic theory of `ℕ` and `ℤ`

which, in particular, is not typeclass-mediated. This is useful to set up the algebra and finiteness

libraries in mathlib (naturals and integers show up as indices/offsets in lists, cardinality in

finsets, powers in groups, ...).

Less basic uses of `ℕ` and `ℤ` should however use the typeclass-mediated development.

The relevant files are:

* `Mathlib/Data/Nat/Basic.lean` for the continuation of the home-baked development on `ℕ`

* `Mathlib/Data/Int/Init.lean` for the continuation of the home-baked development on `ℤ`

* `Mathlib/Algebra/Group/Nat/Defs.lean` for the monoid instances on `ℕ`

-- INSTANCE (free from Core): on

-- INSTANCE (free from Core): on

-- INSTANCE (free from Core): on

-- INSTANCE (free from Core): on

-- INSTANCE (free from Core): on

-- INSTANCE (free from Core): on

-- INSTANCE (free from Core): on

-/

assert_not_exists Monoid

open Function

namespace Nat

variable {a b c d e m n k : ℕ} {p : ℕ → Prop}

/-! ### `succ`, `pred` -/

lemma succ_pos' : 0 < succ n := succ_pos n

alias _root_.LT.lt.nat_succ_le := succ_le_of_lt

alias ⟨of_le_succ, _⟩ := le_succ_iff

-- DISSOLVED: two_lt_of_ne

-- DISSOLVED: two_le_iff

/-! ### `add` -/

/-! ### `sub` -/

/-! ### `mul` -/

lemma mul_def : Nat.mul m n = m * n := mul_eq

lemma two_mul_ne_two_mul_add_one : 2 * n ≠ 2 * m + 1 :=
  mt (congrArg (· % 2))
    (by rw [Nat.add_comm, add_mul_mod_self_left, mul_mod_right, mod_eq_of_lt] <;> simp)

/-! ### `div` -/

lemma le_div_two_iff_mul_two_le {n m : ℕ} : m ≤ n / 2 ↔ (m : ℤ) * 2 ≤ n := by
  rw [Nat.le_div_iff_mul_le Nat.zero_lt_two, ← Int.ofNat_le, Int.natCast_mul, Int.ofNat_two]

lemma div_lt_self' (a b : ℕ) : (a + 1) / (b + 2) < a + 1 :=
  Nat.div_lt_self (Nat.succ_pos _) (Nat.succ_lt_succ (Nat.succ_pos _))

lemma two_mul_odd_div_two (hn : n % 2 = 1) : 2 * (n / 2) = n - 1 := by
  lia

/-! ### `pow` -/

lemma one_le_pow' (n m : ℕ) : 1 ≤ (m + 1) ^ n := one_le_pow n (m + 1) (succ_pos m)

alias sq_sub_sq := pow_two_sub_pow_two

/-!
### Recursion and induction principles

This section is here due to dependencies -- the lemmas here require some of the lemmas
proved above, and some of the results in later sections depend on the definitions in this section.
-/
