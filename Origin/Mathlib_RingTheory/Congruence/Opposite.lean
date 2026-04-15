/-
Extracted from RingTheory/Congruence/Opposite.lean
Genuine: 2 of 4 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

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
