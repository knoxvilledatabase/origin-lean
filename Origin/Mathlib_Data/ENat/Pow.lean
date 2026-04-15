/-
Extracted from Data/ENat/Pow.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Powers of extended natural numbers

We define the power of an extended natural `x : ℕ∞` by another extended natural `y : ℕ∞`. The
definition is chosen such that `x ^ y` is the cardinality of `α → β`, when `β` has cardinality `x`
and `α` has cardinality `y`:

* When `y` is finite, it coincides with the exponentiation by natural numbers (e.g. `⊤ ^ 0 = 1`).
* We set `0 ^ ⊤ = 0`, `1 ^ ⊤ = 1` and `x ^ ⊤ = ⊤` for `x > 1`.

## Naming convention

The quantity `x ^ y` for `x`, `y : ℕ∞` is defined as a `Pow` instance. It is called `epow` in
lemmas' names.
-/

namespace ENat

variable {x y z : ℕ∞}

-- INSTANCE (free from Core): :

lemma epow_def {x y : ℕ∞} :
    x ^ y = if y < ⊤ then x ^ y.toNat else if x = 0 then 0 else if x = 1 then 1 else ⊤ := by
  cases y with
  | top => simp only [lt_self_iff_false, ↓reduceIte]; rfl
  | coe n => simp only [coe_lt_top, ↓reduceIte, toNat_coe]; rfl
