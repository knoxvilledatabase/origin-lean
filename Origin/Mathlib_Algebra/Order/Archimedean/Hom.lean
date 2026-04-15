/-
Extracted from Algebra/Order/Archimedean/Hom.lean
Genuine: 4 of 7 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
### Uniqueness of ring homomorphisms to archimedean fields.

There is at most one ordered ring homomorphism from a linear ordered field to an archimedean linear
ordered field. Reciprocally, such an ordered ring homomorphism exists when the codomain is further
conditionally complete.
-/

assert_not_exists Finset

variable {α β : Type*} [Field α] [LinearOrder α] [Field β] [LinearOrder β]

-- INSTANCE (free from Core): OrderRingHom.subsingleton

-- INSTANCE (free from Core): OrderRingIso.subsingleton_right

-- INSTANCE (free from Core): OrderRingIso.subsingleton_left

theorem OrderRingHom.eq_id [IsStrictOrderedRing α] [Archimedean α] (f : α →+*o α) : f = .id _ :=
  Subsingleton.elim ..

theorem OrderRingIso.eq_refl [IsStrictOrderedRing α] [Archimedean α] (f : α ≃+*o α) : f = .refl _ :=
  Subsingleton.elim ..

theorem OrderRingHom.apply_eq_self [IsStrictOrderedRing α] [Archimedean α] (f : α →+*o α) (x : α) :
    f x = x := by
  rw [f.eq_id]; rfl

theorem OrderRingIso.apply_eq_self [IsStrictOrderedRing α] [Archimedean α] (f : α ≃+*o α) (x : α) :
    f x = x :=
  f.toOrderRingHom.apply_eq_self x
