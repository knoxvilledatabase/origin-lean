/-
Extracted from Algebra/Ring/Shrink.lean
Genuine: 1 of 16 | Dissolved: 0 | Infrastructure: 15
-/
import Origin.Core

/-!
# Transfer ring structures from `α` to `Shrink α`
-/

noncomputable section

namespace Shrink

universe v

variable {α : Type*} [Small.{v} α]

variable (α) in

def ringEquiv [Add α] [Mul α] : Shrink.{v} α ≃+* α := (equivShrink α).symm.ringEquiv

-- INSTANCE (free from Core): [NonUnitalNonAssocSemiring

-- INSTANCE (free from Core): [NonUnitalSemiring

-- INSTANCE (free from Core): [AddMonoidWithOne

-- INSTANCE (free from Core): [AddGroupWithOne

-- INSTANCE (free from Core): [NonAssocSemiring

-- INSTANCE (free from Core): [Semiring

-- INSTANCE (free from Core): [NonUnitalCommSemiring

-- INSTANCE (free from Core): [CommSemiring

-- INSTANCE (free from Core): [NonUnitalNonAssocRing

-- INSTANCE (free from Core): [NonUnitalRing

-- INSTANCE (free from Core): [NonAssocRing

-- INSTANCE (free from Core): [Ring

-- INSTANCE (free from Core): [NonUnitalCommRing

-- INSTANCE (free from Core): [CommRing

-- INSTANCE (free from Core): [Semiring

end Shrink
