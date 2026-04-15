/-
Extracted from Data/List/SplitLengths.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Splitting a list to chunks of specified lengths

This file defines splitting a list to chunks of given lengths, and some proofs about that.
-/

variable {α : Type*} (l : List α) (sz : List ℕ)

namespace List

def splitLengths : List ℕ → List α → List (List α)
  | [], _ => []
  | n::ns, x =>
    let (x0, x1) := x.splitAt n
    x0 :: ns.splitLengths x1
