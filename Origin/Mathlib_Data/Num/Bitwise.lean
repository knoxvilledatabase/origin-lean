/-
Extracted from Data/Num/Bitwise.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Bitwise operations using binary representation of integers

## Definitions

* bitwise operations for `PosNum` and `Num`,
* `SNum`, a type that represents integers as a bit string with a sign bit at the end,
* arithmetic operations for `SNum`.
-/

open List (Vector)

namespace PosNum

def lor : PosNum → PosNum → PosNum
  | 1, bit0 q => bit1 q
  | 1, q => q
  | bit0 p, 1 => bit1 p
  | p, 1 => p
  | bit0 p, bit0 q => bit0 (lor p q)
  | bit0 p, bit1 q => bit1 (lor p q)
  | bit1 p, bit0 q => bit1 (lor p q)
  | bit1 p, bit1 q => bit1 (lor p q)

-- INSTANCE (free from Core): :
