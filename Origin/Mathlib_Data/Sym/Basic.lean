/-
Extracted from Data/Sym/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Symmetric powers

This file defines symmetric powers of a type.  The nth symmetric power
consists of homogeneous n-tuples modulo permutations by the symmetric
group.

The special case of 2-tuples is called the symmetric square, which is
addressed in more detail in `Data.Sym.Sym2`.

TODO: This was created as supporting material for `Sym2`; it
needs a fleshed-out interface.

## Tags

symmetric powers

-/

assert_not_exists MonoidWithZero

open List (Vector)

open Function

def Sym (α : Type*) (n : ℕ) :=
  { s : Multiset α // Multiset.card s = n }

deriving [DecidableEq α] → DecidableEq _
