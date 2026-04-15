/-
Extracted from Data/Nat/BinaryRec.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Binary recursion on `Nat`

This file defines binary recursion on `Nat`.

## Main results
* `Nat.binaryRec`: A recursion principle for `bit` representations of natural numbers.
* `Nat.binaryRec'`: The same as `binaryRec`, but the induction step can assume that if `n=0`,
  the bit being appended is `true`.
* `Nat.binaryRecFromOne`: The same as `binaryRec`, but special casing both 0 and 1 as base cases.
-/

universe u

namespace Nat

def bit (b : Bool) (n : Nat) : Nat :=
  cond b (2 * n + 1) (2 * n)
