/-
Extracted from Data/DList/Instances.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Traversable instance for DLists

This file provides the equivalence between `List α` and `DList α` and the traversable instance
for `DList`.
-/

open Function Equiv

namespace Batteries

variable (α : Type*)

def DList.listEquivDList : List α ≃ DList α where
  toFun := DList.ofList
  invFun := DList.toList
  left_inv _ := DList.toList_ofList _
  right_inv _ := DList.ofList_toList _

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

end Batteries
