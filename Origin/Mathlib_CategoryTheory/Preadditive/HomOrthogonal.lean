/-
Extracted from CategoryTheory/Preadditive/HomOrthogonal.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Hom orthogonal families.

A family of objects in a category with zero morphisms is "hom orthogonal" if the only
morphism between distinct objects is the zero morphism.

We show that in any category with zero morphisms and finite biproducts,
a morphism between biproducts drawn from a hom orthogonal family `s : ι → C`
can be decomposed into a block diagonal matrix with entries in the endomorphism rings of the `s i`.

When the category is preadditive, this decomposition is an additive equivalence,
and intertwines composition and matrix multiplication.
When the category is `R`-linear, the decomposition is an `R`-linear equivalence.

If every object in the hom orthogonal family has an endomorphism ring with invariant basis number
(e.g. if each object in the family is simple, so its endomorphism ring is a division ring,
or otherwise if each endomorphism ring is commutative),
then decompositions of an object as a biproduct of the family have uniquely defined multiplicities.
We state this as:
```
theorem HomOrthogonal.equiv_of_iso (o : HomOrthogonal s) {f : α → ι} {g : β → ι}
    (i : (⨁ fun a => s (f a)) ≅ ⨁ fun b => s (g b)) : ∃ e : α ≃ β, ∀ a, g (e a) = f a
```

This is preliminary to defining semisimple categories.
-/

open Matrix CategoryTheory.Limits

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

def HomOrthogonal {ι : Type*} (s : ι → C) : Prop :=
  Pairwise fun i j => Subsingleton (s i ⟶ s j)

namespace HomOrthogonal

variable {ι : Type*} {s : ι → C}

theorem eq_zero [HasZeroMorphisms C] (o : HomOrthogonal s) {i j : ι} (w : i ≠ j) (f : s i ⟶ s j) :
    f = 0 :=
  (o w).elim _ _

variable [HasZeroMorphisms C] [HasFiniteBiproducts C]

open scoped Classical in
