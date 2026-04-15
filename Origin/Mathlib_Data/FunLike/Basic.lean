/-
Extracted from Data/FunLike/Basic.lean
Genuine: 3 of 4 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

public meta import Lean.Meta.CoeAttr

/-!
# Typeclass for a type `F` with an injective map to `A → B`

This typeclass is primarily for use by homomorphisms like `MonoidHom` and `LinearMap`.

There is the "D"ependent version `DFunLike` and the non-dependent version `FunLike`.

## Basic usage of `DFunLike` and `FunLike`

A typical type of morphisms should be declared as:
```
structure MyHom (A B : Type*) [MyClass A] [MyClass B] where
  (toFun : A → B)
  (map_op' : ∀ (x y : A), toFun (MyClass.op x y) = MyClass.op (toFun x) (toFun y))

namespace MyHom

variable (A B : Type*) [MyClass A] [MyClass B]

instance : FunLike (MyHom A B) A B where
  coe := MyHom.toFun
  coe_injective' := fun f g h => by cases f; cases g; congr

@[ext] theorem ext {f g : MyHom A B} (h : ∀ x, f x = g x) : f = g := DFunLike.ext f g h

/-- Copy of a `MyHom` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/

protected def copy (f : MyHom A B) (f' : A → B) (h : f' = ⇑f) : MyHom A B where
  toFun := f'
  map_op' := h.symm ▸ f.map_op'

end MyHom

```

-- INSTANCE (free from Core): and

extensionality and simp lemmas.

## Morphism classes extending `DFunLike` and `FunLike`

The `FunLike` design provides further benefits if you put in a bit more work.

The first step is to extend `FunLike` to create a class of those types satisfying

the axioms of your new type of morphisms.

Continuing the example above:

```

class MyHomClass (F : Type*) (A B : outParam Type*) [MyClass A] [MyClass B]
    [FunLike F A B] : Prop :=
  (map_op : ∀ (f : F) (x y : A), f (MyClass.op x y) = MyClass.op (f x) (f y))
