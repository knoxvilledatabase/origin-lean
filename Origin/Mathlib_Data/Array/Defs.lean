/-
Extracted from Data/Array/Defs.lean
Genuine: 2 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Init

/-!
## Definitions on Arrays

This file contains various definitions on `Array`. It does not contain
proofs about these definitions, those are contained in other files in `Mathlib.Data.Array`.
-/

namespace Array

universe u

variable {α : Type u}

def cyclicPermute! [Inhabited α] : Array α → List Nat → Array α
  | a, []      => a
  | a, i :: is => cyclicPermuteAux a is a[i]! i
where cyclicPermuteAux : Array α → List Nat → α → Nat → Array α
| a, [], x, i0 => a.set! i0 x
| a, i :: is, x, i0 =>
  let (y, a) := a.swapAt! i x
  cyclicPermuteAux a is y i0

def permute! [Inhabited α] (a : Array α) (ls : List (List Nat)) : Array α :=

ls.foldl (init := a) (·.cyclicPermute! ·)

end Array
