/-
Extracted from Data/ZMod/Basic.lean
Genuine: 1 of 6 | Dissolved: 3 | Infrastructure: 2
-/
import Origin.Core

/-!
# Integers mod `n`

Definition of the integers mod n, and the field structure on the integers mod p.


## Definitions

* `ZMod n`, which is for integers modulo a nat `n : ℕ`

* `val a` is defined as a natural number:
  - for `a : ZMod 0` it is the absolute value of `a`
  - for `a : ZMod n` with `0 < n` it is the least natural number in the equivalence class

* A coercion `cast` is defined from `ZMod n` into any ring.
  This is a ring hom if the ring has characteristic dividing `n`

-/

assert_not_exists Field Submodule TwoSidedIdeal

open Function ZMod

namespace ZMod

-- INSTANCE (free from Core): :

-- DISSOLVED: finEquiv

-- INSTANCE (free from Core): charZero

def val : ∀ {n : ℕ}, ZMod n → ℕ
  | 0 => Int.natAbs
  | n + 1 => ((↑) : Fin (n + 1) → ℕ)

-- DISSOLVED: val_lt

grind_pattern val_lt => a.val

-- DISSOLVED: val_le
