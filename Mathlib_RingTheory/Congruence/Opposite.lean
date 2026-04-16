/-
Extracted from RingTheory/Congruence/Opposite.lean
Genuine: 3 | Conflates: 0 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.GroupTheory.Congruence.Opposite

noncomputable section

/-!
# Congruences on the opposite ring

This file defines the order isomorphism between the congruences on a ring `R` and the congruences on
the opposite ring `Rᵐᵒᵖ`.

-/

variable {R : Type*} [Add R] [Mul R]

namespace RingCon

def op (c : RingCon R) : RingCon Rᵐᵒᵖ where
  __ := c.toCon.op
  mul' h1 h2 := c.toCon.op.mul h1 h2
  add' h1 h2 := c.add h1 h2

def unop (c : RingCon Rᵐᵒᵖ) : RingCon R where
  __ := c.toCon.unop
  mul' h1 h2 := c.toCon.unop.mul h1 h2
  add' h1 h2 := c.add h1 h2

@[simps]
def opOrderIso : RingCon R ≃o RingCon Rᵐᵒᵖ where
  toFun := op
  invFun := unop
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' {c d} := by rw [le_def, le_def]; constructor <;> intro h _ _ h' <;> exact h h'

end RingCon
