/-
Extracted from Algebra/Ring/Action/Submonoid.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The subgroup of fixed points of an action
-/

variable (M α : Type*) [Monoid M]

section AddMonoid

variable [AddMonoid α] [DistribMulAction M α]

def FixedPoints.addSubmonoid : AddSubmonoid α where
  carrier := MulAction.fixedPoints M α
  zero_mem' := smul_zero
  add_mem' ha hb _ := by rw [smul_add, ha, hb]
