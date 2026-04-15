/-
Extracted from CategoryTheory/Linear/Basic.lean
Genuine: 1 of 6 | Dissolved: 0 | Infrastructure: 5
-/
import Origin.Core

/-!
# Linear categories

An `R`-linear category is a category in which `X ⟶ Y` is an `R`-module in such a way that
composition of morphisms is `R`-linear in both variables.

Note that sometimes in the literature a "linear category" is further required to be abelian.

## Implementation

Corresponding to the fact that we need to have an `AddCommGroup X` structure in place
to talk about a `Module R X` structure,
we need `Preadditive C` as a prerequisite typeclass for `Linear R C`.
This makes for longer signatures than would be ideal.

## Future work

It would be nice to have a usable framework of enriched categories in which this would just be
a category enriched in `Module R`.

-/

universe w v u

open CategoryTheory.Limits

open LinearMap

namespace CategoryTheory

class Linear (R : Type w) [Semiring R] (C : Type u) [Category.{v} C] [Preadditive C] where
  homModule : ∀ X Y : C, Module R (X ⟶ Y) := by infer_instance
  /-- compatibility of the scalar multiplication with the post-composition -/
  smul_comp : ∀ (X Y Z : C) (r : R) (f : X ⟶ Y) (g : Y ⟶ Z), (r • f) ≫ g = r • f ≫ g := by
    cat_disch
  /-- compatibility of the scalar multiplication with the pre-composition -/
  comp_smul : ∀ (X Y Z : C) (f : X ⟶ Y) (r : R) (g : Y ⟶ Z), f ≫ (r • g) = r • f ≫ g := by
    cat_disch

attribute [instance_reducible, instance] Linear.homModule

attribute [simp] Linear.smul_comp Linear.comp_smul

end CategoryTheory

open CategoryTheory

namespace CategoryTheory.Linear

variable {C : Type u} [Category.{v} C] [Preadditive C]

-- INSTANCE (free from Core): preadditiveNatLinear

-- INSTANCE (free from Core): preadditiveIntLinear

section End

variable {R : Type w}

-- INSTANCE (free from Core): [Semiring

-- INSTANCE (free from Core): [CommSemiring

end End

variable {R : Type w} [Semiring R] [Linear R C]

section InducedCategory

universe u'

variable {D : Type u'} (F : D → C)

-- INSTANCE (free from Core): inducedCategory

variable {F} in
