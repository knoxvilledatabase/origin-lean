/-
Extracted from Data/Set/Semiring.lean
Genuine: 4 | Conflates: 0 | Dissolved: 0 | Infrastructure: 40
-/
import Origin.Core
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Algebra.Order.Kleene
import Mathlib.Algebra.Order.Ring.Canonical

noncomputable section

/-!
# Sets as a semiring under union

This file defines `SetSemiring α`, an alias of `Set α`, which we endow with `∪` as addition and
pointwise `*` as multiplication. If `α` is a (commutative) monoid, `SetSemiring α` is a
(commutative) semiring.
-/

open Function Set

open Pointwise

variable {α β : Type*}

def SetSemiring (α : Type*) : Type _ :=
  Set α

noncomputable instance (α : Type*) : Inhabited (SetSemiring α) :=
  (inferInstance : Inhabited (Set _))

instance (α : Type*) : PartialOrder (SetSemiring α) :=
  (inferInstance : PartialOrder (Set _))

instance (α : Type*) : OrderBot (SetSemiring α) :=
  (inferInstance : OrderBot (Set _))

protected def Set.up : Set α ≃ SetSemiring α :=
  Equiv.refl _

namespace SetSemiring

protected def down : SetSemiring α ≃ Set α :=
  Equiv.refl _

open SetSemiring (down)

open Set (up)

instance : Zero (SetSemiring α) where zero := Set.up (∅ : Set α)

instance : Add (SetSemiring α) where add s t := Set.up (SetSemiring.down s ∪ SetSemiring.down t)

instance : AddCommMonoid (SetSemiring α) where
  add_assoc := union_assoc
  zero_add := empty_union
  add_zero := union_empty
  add_comm := union_comm
  nsmul := nsmulRec

instance addLeftMono : AddLeftMono (SetSemiring α) :=
  ⟨fun _ _ _ => union_subset_union_right _⟩

section Mul

variable [Mul α]

instance : NonUnitalNonAssocSemiring (SetSemiring α) :=
  { (inferInstance : AddCommMonoid (SetSemiring α)) with
    mul := fun s t => Set.up (image2 (· * ·) (SetSemiring.down s) (SetSemiring.down t))
    zero_mul := fun _ => empty_mul
    mul_zero := fun _ => mul_empty
    left_distrib := fun _ _ _ => mul_union
    right_distrib := fun _ _ _ => union_mul }

instance : NoZeroDivisors (SetSemiring α) :=
  ⟨fun {a b} ab =>
    a.eq_empty_or_nonempty.imp_right fun ha =>
      b.eq_empty_or_nonempty.resolve_right fun hb =>
        Nonempty.ne_empty ⟨_, mul_mem_mul ha.some_mem hb.some_mem⟩ ab⟩

instance mulLeftMono : MulLeftMono (SetSemiring α) :=
  ⟨fun _ _ _ => mul_subset_mul_left⟩

instance mulRightMono : MulRightMono (SetSemiring α) :=
  ⟨fun _ _ _ => mul_subset_mul_right⟩

end Mul

section One

variable [One α]

instance : One (SetSemiring α) where one := Set.up (1 : Set α)

@[simp]
theorem down_one : down (1 : SetSemiring α) = 1 :=
  rfl

end One

instance [MulOneClass α] : NonAssocSemiring (SetSemiring α) :=
  { (inferInstance : NonUnitalNonAssocSemiring (SetSemiring α)),
    Set.mulOneClass with }

instance [Semigroup α] : NonUnitalSemiring (SetSemiring α) :=
  { (inferInstance : NonUnitalNonAssocSemiring (SetSemiring α)), Set.semigroup with }

instance [Monoid α] : IdemSemiring (SetSemiring α) :=
  { (inferInstance : NonAssocSemiring (SetSemiring α)),
    (inferInstance : NonUnitalSemiring (SetSemiring α)),
    (inferInstance : CompleteBooleanAlgebra (Set α)) with }

instance [CommSemigroup α] : NonUnitalCommSemiring (SetSemiring α) :=
  { (inferInstance : NonUnitalSemiring (SetSemiring α)), Set.commSemigroup with }

instance [CommMonoid α] : IdemCommSemiring (SetSemiring α) :=
  { (inferInstance : IdemSemiring (SetSemiring α)),
    (inferInstance : CommMonoid (Set α)) with }

instance [CommMonoid α] : CommMonoid (SetSemiring α) :=
  { (inferInstance : Monoid (SetSemiring α)), Set.commSemigroup with }

instance [CommMonoid α] : CanonicallyOrderedCommSemiring (SetSemiring α) :=
  { (inferInstance : Semiring (SetSemiring α)), (inferInstance : CommMonoid (SetSemiring α)),
    (inferInstance : PartialOrder (SetSemiring α)), (inferInstance : OrderBot (SetSemiring α)),
    (inferInstance : NoZeroDivisors (SetSemiring α)) with
    add_le_add_left := fun _ _ => add_le_add_left
    exists_add_of_le := fun {_ b} ab => ⟨b, (union_eq_right.2 ab).symm⟩
    le_self_add := fun _ _ => subset_union_left }

def imageHom [MulOneClass α] [MulOneClass β] (f : α →* β) : SetSemiring α →+* SetSemiring β where
  toFun s := up (image f (down s))
  map_zero' := image_empty _
  map_one' := by
    dsimp only  -- Porting note: structures do not do this automatically any more
    rw [down_one, image_one, map_one, singleton_one, up_one]
  map_add' := image_union _
  map_mul' _ _ := image_mul f

end SetSemiring
