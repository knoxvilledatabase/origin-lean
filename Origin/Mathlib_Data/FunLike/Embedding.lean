/-
Extracted from Data/FunLike/Embedding.lean
Genuine: 14 | Conflates: 0 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core
import Mathlib.Data.FunLike.Basic

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

This file will then provide a `CoeFun` instance and various

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

@[simp]
lemma map_op {F A B : Type*} [MyClass A] [MyClass B] [FunLike F A B] [MyEmbeddingClass F A B]
    (f : F) (x y : A) :
    f (MyClass.op x y) = MyClass.op (f x) (f y) :=
  MyEmbeddingClass.map_op _ _ _

namespace MyEmbedding

variable {A B : Type*} [MyClass A] [MyClass B]

instance : MyEmbeddingClass (MyEmbedding A B) A B where
  injective' := MyEmbedding.injective'
  map_op := MyEmbedding.map_op'

end MyEmbedding

```

The second step is to add instances of your new `MyEmbeddingClass` for all types extending

`MyEmbedding`.

Typically, you can just declare a new class analogous to `MyEmbeddingClass`:

```

structure CoolerEmbedding (A B : Type*) [CoolClass A] [CoolClass B] extends MyEmbedding A B where
  (map_cool' : toFun CoolClass.cool = CoolClass.cool)

class CoolerEmbeddingClass (F : Type*) (A B : outParam Type*) [CoolClass A] [CoolClass B]
    [FunLike F A B]
    extends MyEmbeddingClass F A B where
  (map_cool : ∀ (f : F), f CoolClass.cool = CoolClass.cool)

@[simp]
lemma map_cool {F A B : Type*} [CoolClass A] [CoolClass B]
    [FunLike F A B] [CoolerEmbeddingClass F A B] (f : F) :
    f CoolClass.cool = CoolClass.cool :=
  CoolerEmbeddingClass.map_cool _

variable {A B : Type*} [CoolClass A] [CoolClass B]

instance : FunLike (CoolerEmbedding A B) A B where
  coe f := f.toFun
  coe_injective' f g h := by cases f; cases g; congr; apply DFunLike.coe_injective; congr

instance : CoolerEmbeddingClass (CoolerEmbedding A B) A B where
  injective' f := f.injective'
  map_op f := f.map_op'
  map_cool f := f.map_cool'

```

Then any declaration taking a specific type of morphisms as parameter can instead take the

class you just defined:

```

lemma do_something {F : Type*} [FunLike F A B] [MyEmbeddingClass F A B] (f : F) : sorry := sorry

```

This means anything set up for `MyEmbedding`s will automatically work for `CoolerEmbeddingClass`es,

and defining `CoolerEmbeddingClass` only takes a constant amount of effort,

instead of linearly increasing the work per `MyEmbedding`-related declaration.

-/

class EmbeddingLike (F : Sort*) (α β : outParam (Sort*)) [FunLike F α β] : Prop where
  /-- The coercion to functions must produce injective functions. -/
  injective' : ∀ f : F, Function.Injective (DFunLike.coe f)

namespace EmbeddingLike

variable {F α β γ : Sort*} [FunLike F α β] [i : EmbeddingLike F α β]

protected theorem injective (f : F) : Function.Injective f :=
  injective' f

@[simp]
theorem apply_eq_iff_eq (f : F) {x y : α} : f x = f y ↔ x = y :=
  (EmbeddingLike.injective f).eq_iff

@[simp]
theorem comp_injective {F : Sort*} [FunLike F β γ] [EmbeddingLike F β γ] (f : α → β) (e : F) :
    Function.Injective (e ∘ f) ↔ Function.Injective f :=
  (EmbeddingLike.injective e).of_comp_iff f

end EmbeddingLike
