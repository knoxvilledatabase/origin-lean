/-
Extracted from Data/Nat/PSub.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Partial predecessor and partial subtraction on the natural numbers

The usual definition of natural number subtraction (`Nat.sub`) returns 0 as a "garbage value" for
`a - b` when `a < b`. Similarly, `Nat.pred 0` is defined to be `0`. The functions in this file
wrap the result in an `Option` type instead:

## Main definitions

- `Nat.ppred`: a partial predecessor operation
- `Nat.psub`: a partial subtraction operation

-/

namespace Nat

def ppred : ℕ → Option ℕ
  | 0 => none
  | n + 1 => some n
