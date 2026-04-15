/-
Extracted from Data/FunLike/Embedding.lean
Genuine: 3 of 4 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Typeclass for a type `F` with an injective map to `A ↪ B`

This typeclass is primarily for use by embeddings such as `RelEmbedding`.

## Basic usage of `EmbeddingLike`

A typical type of embeddings should be declared as:
```
structure MyEmbedding (A B : Type*) [MyClass A] [MyClass B] where
  (toFun : A → B)
  (injective' : Function.Injective toFun)
  (map_op' : ∀ (x y : A), toFun (MyClass.op x y) = MyClass.op (toFun x) (toFun y))

namespace MyEmbedding

variable (A B : Type*) [MyClass A] [MyClass B]

instance : FunLike (MyEmbedding A B) A B where
  coe := MyEmbedding.toFun
  coe_injective' := fun f g h ↦ by cases f; cases g; congr

-- This instance is optional if you follow the "Embedding class" design below:
instance : EmbeddingLike (MyEmbedding A B) A B where
  injective' := MyEmbedding.injective'

@[ext] theorem ext {f g : MyEmbedding A B} (h : ∀ x, f x = g x) : f = g := DFunLike.ext f g h

/-- Copy of a `MyEmbedding` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/

protected def copy (f : MyEmbedding A B) (f' : A → B) (h : f' = ⇑f) : MyEmbedding A B :=
  { toFun := f'
    injective' := h.symm ▸ f.injective'
    map_op' := h.symm ▸ f.map_op' }

end MyEmbedding

```

-- INSTANCE (free from Core): and

extensionality and simp lemmas.

## Embedding classes extending `EmbeddingLike`

The `EmbeddingLike` design provides further benefits if you put in a bit more work.

The first step is to extend `EmbeddingLike` to create a class of those types satisfying

the axioms of your new type of morphisms.

Continuing the example above:

```

class MyEmbeddingClass (F : Type*) (A B : outParam Type*) [MyClass A] [MyClass B]
    [FunLike F A B]
    extends EmbeddingLike F A B where
  map_op : ∀ (f : F) (x y : A), f (MyClass.op x y) = MyClass.op (f x) (f y)
