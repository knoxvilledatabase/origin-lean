/-
Extracted from Algebra/Order/Hom/Basic.lean
Genuine: 4 of 9 | Dissolved: 0 | Infrastructure: 5
-/
import Origin.Core

/-!
# Algebraic order homomorphism classes

This file defines hom classes for common properties at the intersection of order theory and algebra.

## Typeclasses

Basic typeclasses
* `NonnegHomClass`: Homs are nonnegative: `∀ f a, 0 ≤ f a`
* `SubadditiveHomClass`: Homs are subadditive: `∀ f a b, f (a + b) ≤ f a + f b`
* `SubmultiplicativeHomClass`: Homs are submultiplicative: `∀ f a b, f (a * b) ≤ f a * f b`
* `MulLEAddHomClass`: `∀ f a b, f (a * b) ≤ f a + f b`
* `NonarchimedeanHomClass`: `∀ a b, f (a + b) ≤ max (f a) (f b)`

Group norms
* `AddGroupSeminormClass`: Homs are nonnegative, subadditive, even and preserve zero.
* `GroupSeminormClass`: Homs are nonnegative, respect `f (a * b) ≤ f a + f b`, `f a⁻¹ = f a` and
  preserve zero.
* `AddGroupNormClass`: Homs are seminorms such that `f x = 0 → x = 0` for all `x`.
* `GroupNormClass`: Homs are seminorms such that `f x = 0 → x = 1` for all `x`.

Ring norms
* `RingSeminormClass`: Homs are submultiplicative group norms.
* `RingNormClass`: Homs are ring seminorms that are also additive group norms.
* `MulRingSeminormClass`: Homs are ring seminorms that are multiplicative.
* `MulRingNormClass`: Homs are ring norms that are multiplicative.

## Notes

Typeclasses for seminorms are defined here while types of seminorms are defined in
`Analysis.Normed.Group.Seminorm` and `Analysis.Normed.Ring.Seminorm` because absolute values are
multiplicative ring norms but outside of this use we only consider real-valued seminorms.

## TODO

Finitary versions of the current lemmas.
-/

assert_not_exists Field

library_note «out-param inheritance» /--

Diamond inheritance cannot depend on `outParam`s in the following circumstances:

* there are three classes `Top`, `Middle`, `Bottom`

* all of these classes have a parameter `(α : outParam _)`

-- INSTANCE (free from Core): parameter

* the `Root` class has two child classes: `Left` and `Right`, these are siblings in the hierarchy

-- INSTANCE (free from Core): `Bottom.toMiddle`

-- INSTANCE (free from Core): `Middle.toTop`

* there is a `Leaf` class that inherits from both `Left` and `Right`.

In that case, given instances `Bottom α` and `Leaf α`, Lean cannot synthesize a `Top α` instance,

even though the hypotheses of the instances `Bottom.toMiddle` and `Middle.toTop` are satisfied.

There are two workarounds:

-- INSTANCE (free from Core): `Middle.toTop`

-- INSTANCE (free from Core): by

-/

open Function

variable {ι F α β γ δ : Type*}

/-! ### Basics -/

class NonnegHomClass (F : Type*) (α β : outParam Type*) [Zero β] [LE β] [FunLike F α β] : Prop where
  /-- the image of any element is nonnegative. -/
  apply_nonneg (f : F) : ∀ a, 0 ≤ f a

class SubadditiveHomClass (F : Type*) (α β : outParam Type*)
    [Add α] [Add β] [LE β] [FunLike F α β] : Prop where
  /-- the image of a sum is less or equal than the sum of the images. -/
  map_add_le_add (f : F) : ∀ a b, f (a + b) ≤ f a + f b
