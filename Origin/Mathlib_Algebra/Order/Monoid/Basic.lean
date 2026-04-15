/-
Extracted from Algebra/Order/Monoid/Basic.lean
Genuine: 6 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Group.InjSurj
import Mathlib.Order.Hom.Basic

/-!
# Ordered monoids

This file develops some additional material on ordered monoids.
-/

open Function

universe u

variable {α : Type u} {β : Type*}

@[to_additive "Pullback an `OrderedAddCommMonoid` under an injective map."]
abbrev Function.Injective.orderedCommMonoid [OrderedCommMonoid α] {β : Type*} [One β] [Mul β]
    [Pow β ℕ] (f : β → α) (hf : Function.Injective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) :
    OrderedCommMonoid β where
  toCommMonoid := hf.commMonoid f one mul npow
  toPartialOrder := PartialOrder.lift f hf
  mul_le_mul_left a b ab c := show f (c * a) ≤ f (c * b) by
    rw [mul, mul]; apply mul_le_mul_left'; exact ab

@[to_additive Function.Injective.orderedCancelAddCommMonoid
    "Pullback an `OrderedCancelAddCommMonoid` under an injective map."]
abbrev Function.Injective.orderedCancelCommMonoid [OrderedCancelCommMonoid α] [One β] [Mul β]
    [Pow β ℕ] (f : β → α) (hf : Injective f) (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) : OrderedCancelCommMonoid β where
  toOrderedCommMonoid := hf.orderedCommMonoid f one mul npow
  le_of_mul_le_mul_left a b c (bc : f (a * b) ≤ f (a * c)) :=
    (mul_le_mul_iff_left (f a)).1 (by rwa [← mul, ← mul])

@[to_additive "Pullback an `OrderedAddCommMonoid` under an injective map."]
abbrev Function.Injective.linearOrderedCommMonoid [LinearOrderedCommMonoid α] {β : Type*} [One β]
    [Mul β] [Pow β ℕ] [Max β] [Min β] (f : β → α) (hf : Function.Injective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (sup : ∀ x y, f (x ⊔ y) = max (f x) (f y)) (inf : ∀ x y, f (x ⊓ y) = min (f x) (f y)) :
    LinearOrderedCommMonoid β where
  toOrderedCommMonoid := hf.orderedCommMonoid f one mul npow
  __ := LinearOrder.lift f hf sup inf

@[to_additive Function.Injective.linearOrderedCancelAddCommMonoid
    "Pullback a `LinearOrderedCancelAddCommMonoid` under an injective map."]
abbrev Function.Injective.linearOrderedCancelCommMonoid [LinearOrderedCancelCommMonoid α] [One β]
    [Mul β] [Pow β ℕ] [Max β] [Min β] (f : β → α) (hf : Injective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (hsup : ∀ x y, f (x ⊔ y) = max (f x) (f y)) (hinf : ∀ x y, f (x ⊓ y) = min (f x) (f y)) :
    LinearOrderedCancelCommMonoid β where
  toOrderedCancelCommMonoid := hf.orderedCancelCommMonoid f one mul npow
  __ := hf.linearOrderedCommMonoid f one mul npow hsup hinf

@[to_additive (attr := simps!)
      "The order embedding sending `b` to `a + b`, for some fixed `a`.
       See also `OrderIso.addLeft` when working in an additive ordered group."]
def OrderEmbedding.mulLeft {α : Type*} [Mul α] [LinearOrder α]
    [MulLeftStrictMono α] (m : α) : α ↪o α :=
  OrderEmbedding.ofStrictMono (fun n => m * n) fun _ _ w => mul_lt_mul_left' w m

@[to_additive (attr := simps!)
      "The order embedding sending `b` to `b + a`, for some fixed `a`.
       See also `OrderIso.addRight` when working in an additive ordered group."]
def OrderEmbedding.mulRight {α : Type*} [Mul α] [LinearOrder α]
    [MulRightStrictMono α] (m : α) : α ↪o α :=
  OrderEmbedding.ofStrictMono (fun n => n * m) fun _ _ w => mul_lt_mul_right' w m
