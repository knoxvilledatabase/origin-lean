/-
Extracted from Algebra/Order/Group/Action.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Results about `CovariantClass G α HSMul.hSMul LE.le`

When working with group actions rather than modules, we drop the `0 < c` condition.

Notably these are relevant for pointwise actions on set-like objects.
-/

variable {ι : Sort*} {M α : Type*}

theorem smul_mono_right [SMul M α] [Preorder α] [CovariantClass M α HSMul.hSMul LE.le]
    (m : M) : Monotone (HSMul.hSMul m : α → α) :=
  fun _ _ => CovariantClass.elim _
