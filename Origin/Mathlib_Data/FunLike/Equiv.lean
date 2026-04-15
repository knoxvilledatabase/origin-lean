/-
Extracted from Data/FunLike/Equiv.lean
Genuine: 6 of 8 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Typeclass for a type `F` with an injective map to `A ≃ B`

This typeclass is primarily for use by isomorphisms like `MonoidEquiv` and `LinearEquiv`.

## Basic usage of `EquivLike`

A typical type of isomorphisms should be declared as:
```
structure MyIso (A B : Type*) [MyClass A] [MyClass B] extends Equiv A B where
  (map_op' : ∀ (x y : A), toFun (MyClass.op x y) = MyClass.op (toFun x) (toFun y))

namespace MyIso

variable (A B : Type*) [MyClass A] [MyClass B]

instance instEquivLike : EquivLike (MyIso A B) A B where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by cases f; cases g; congr; exact EquivLike.coe_injective' _ _ h₁ h₂

@[ext] theorem ext {f g : MyIso A B} (h : ∀ x, f x = g x) : f = g := DFunLike.ext f g h

/-- Copy of a `MyIso` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/

protected def copy (f : MyIso A B) (f' : A → B) (f_inv : B → A)
    (h₁ : f' = f) (h₂ : f_inv = f.invFun) : MyIso A B where
  toFun := f'
  invFun := f_inv
  left_inv := h₁.symm ▸ h₂.symm ▸ f.left_inv
  right_inv := h₁.symm ▸ h₂.symm ▸ f.right_inv
  map_op' := h₁.symm ▸ f.map_op'

end MyIso

```

-- INSTANCE (free from Core): and

extensionality and simp lemmas.

## Isomorphism classes extending `EquivLike`

The `EquivLike` design provides further benefits if you put in a bit more work.

The first step is to extend `EquivLike` to create a class of those types satisfying

the axioms of your new type of isomorphisms.

Continuing the example above:

```

class MyIsoClass (F : Type*) (A B : outParam Type*) [MyClass A] [MyClass B]
    [EquivLike F A B]
    extends MyHomClass F A B

namespace MyIso

variable {A B : Type*} [MyClass A] [MyClass B]

-- INSTANCE (free from Core): :

end MyIso

```

The second step is to add instances of your new `MyIsoClass` for all types extending `MyIso`.

Typically, you can just declare a new class analogous to `MyIsoClass`:

```

structure CoolerIso (A B : Type*) [CoolClass A] [CoolClass B] extends MyIso A B where
  (map_cool' : toFun CoolClass.cool = CoolClass.cool)

class CoolerIsoClass (F : Type*) (A B : outParam Type*) [CoolClass A] [CoolClass B]
    [EquivLike F A B]
    extends MyIsoClass F A B where
  (map_cool : ∀ (f : F), f CoolClass.cool = CoolClass.cool)
