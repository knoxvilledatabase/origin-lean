/-
Extracted from Data/ZMod/ValMinAbs.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Absolute value in `ZMod n`
-/

namespace ZMod

variable {n : ℕ} {a b : ZMod n}

def valMinAbs : ∀ {n : ℕ}, ZMod n → ℤ
  | 0, x => x
  | n@(_ + 1), x => if x.val ≤ n / 2 then x.val else (x.val : ℤ) - n
