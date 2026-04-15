/-
Extracted from Data/Int/Log.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Integer logarithms in a field with respect to a natural base

This file defines two `ℤ`-valued analogs of the logarithm of `r : R` with base `b : ℕ`:

* `Int.log b r`: Lower logarithm, or floor **log**. Greatest `k` such that `↑b^k ≤ r`.
* `Int.clog b r`: Upper logarithm, or **c**eil **log**. Least `k` such that `r ≤ ↑b^k`.

Note that `Int.log` gives the position of the left-most non-zero digit:
```lean
#eval (Int.log 10 (0.09 : ℚ), Int.log 10 (0.10 : ℚ), Int.log 10 (0.11 : ℚ))
--    (-2,                    -1,                    -1)
#eval (Int.log 10 (9 : ℚ),    Int.log 10 (10 : ℚ),   Int.log 10 (11 : ℚ))
--    (0,                     1,                     1)
```
which means it can be used for computing digit expansions
```lean
import Data.Fin.VecNotation
import Mathlib.Data.Rat.Floor

def digits (b : ℕ) (q : ℚ) (n : ℕ) : ℕ :=
  ⌊q * ((b : ℚ) ^ (n - Int.log b q))⌋₊ % b

#eval digits 10 (1/7) ∘ ((↑) : Fin 8 → ℕ)
-- ![1, 4, 2, 8, 5, 7, 1, 4]
```

## Main results

* For `Int.log`:
  * `Int.zpow_log_le_self`, `Int.lt_zpow_succ_log_self`: the bounds formed by `Int.log`,
    `(b : R) ^ log b r ≤ r < (b : R) ^ (log b r + 1)`.
  * `Int.zpow_log_gi`: the Galois coinsertion between `zpow` and `Int.log`.
* For `Int.clog`:
  * `Int.zpow_pred_clog_lt_self`, `Int.self_le_zpow_clog`: the bounds formed by `Int.clog`,
    `(b : R) ^ (clog b r - 1) < r ≤ (b : R) ^ clog b r`.
  * `Int.clog_zpow_gi`:  the Galois insertion between `Int.clog` and `zpow`.
* `Int.neg_log_inv_eq_clog`, `Int.neg_clog_inv_eq_log`: the link between the two definitions.
-/

assert_not_exists Finset

variable {R : Type*} [Semifield R] [LinearOrder R] [IsStrictOrderedRing R] [FloorSemiring R]

namespace Int

def log (b : ℕ) (r : R) : ℤ :=
  if 1 ≤ r then Nat.log b ⌊r⌋₊ else -Nat.clog b ⌈r⁻¹⌉₊

omit [IsStrictOrderedRing R] in

theorem log_of_one_le_right (b : ℕ) {r : R} (hr : 1 ≤ r) : log b r = Nat.log b ⌊r⌋₊ :=
  if_pos hr

theorem log_of_right_le_one (b : ℕ) {r : R} (hr : r ≤ 1) : log b r = -Nat.clog b ⌈r⁻¹⌉₊ := by
  obtain rfl | hr := hr.eq_or_lt
  · rw [log, if_pos hr, inv_one, Nat.ceil_one, Nat.floor_one, Nat.log_one_right, Nat.clog_one_right,
      Int.ofNat_zero, neg_zero]
  · exact if_neg hr.not_ge
