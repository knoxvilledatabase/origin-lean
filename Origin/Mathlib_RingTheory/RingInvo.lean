/-
Extracted from RingTheory/RingInvo.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Ring involutions

This file defines a ring involution as a structure extending `R ≃+* Rᵐᵒᵖ`,
with the additional fact `f.involution : (f (f x).unop).unop = x`.

## Notation

We provide a coercion to a function `R → Rᵐᵒᵖ`.

## References

* <https://en.wikipedia.org/wiki/Involution_(mathematics)#Ring_theory>

## Tags

Ring involution
-/

variable {F : Type*} (R : Type*)

structure RingInvo [Semiring R] extends R ≃+* Rᵐᵒᵖ where
  /-- The requirement that the ring homomorphism is its own inverse -/
  involution' : ∀ x, (toFun (toFun x).unop).unop = x

add_decl_doc RingInvo.toRingEquiv

class RingInvoClass (F R : Type*) [Semiring R] [EquivLike F R Rᵐᵒᵖ] : Prop
  extends RingEquivClass F R Rᵐᵒᵖ where
  /-- Every ring involution must be its own inverse -/
  involution : ∀ (f : F) (x), (f (f x).unop).unop = x
