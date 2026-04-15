/-
Extracted from Data/DList/Instances.lean
Genuine: 1 | Conflates: 0 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core
import Batteries.Data.DList.Lemmas
import Mathlib.Control.Traversable.Equiv
import Mathlib.Control.Traversable.Instances

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

instance : Traversable DList :=
  Equiv.traversable DList.listEquivDList

instance : LawfulTraversable DList :=
  Equiv.isLawfulTraversable DList.listEquivDList

instance {α} : Inhabited (DList α) :=
  ⟨DList.empty⟩

end Batteries
