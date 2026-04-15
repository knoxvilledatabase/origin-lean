/-
Extracted from CategoryTheory/Preadditive/Mat.lean
Genuine: 4 of 5 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Matrices over a category.

When `C` is a preadditive category, `Mat_ C` is the preadditive category
whose objects are finite tuples of objects in `C`, and
whose morphisms are matrices of morphisms from `C`.

There is a functor `Mat_.embedding : C ⥤ Mat_ C` sending morphisms to one-by-one matrices.

`Mat_ C` has finite biproducts.

## The additive envelope

We show that this construction is the "additive envelope" of `C`,
in the sense that any additive functor `F : C ⥤ D` to a category `D` with biproducts
lifts to a functor `Mat_.lift F : Mat_ C ⥤ D`,
Moreover, this functor is unique (up to natural isomorphisms) amongst functors `L : Mat_ C ⥤ D`
such that `embedding C ⋙ L ≅ F`.
(As we don't have 2-category theory, we can't explicitly state that `Mat_ C` is
the initial object in the 2-category of categories under `C` which have biproducts.)

As a consequence, when `C` already has finite biproducts we have `Mat_ C ≌ C`.

## Future work

We should provide a more convenient `Mat R`, when `R` is a ring,
as a category with objects `n : FinType`,
and whose morphisms are matrices with components in `R`.

Ideally this would conveniently interact with both `Mat_` and `Matrix`.

-/

open CategoryTheory CategoryTheory.Preadditive

noncomputable section

namespace CategoryTheory

universe w v₁ v₂ u₁ u₂

variable (C : Type u₁) [Category.{v₁} C] [Preadditive C]

structure Mat_ where
  /-- The index type `ι` -/
  ι : Type
  [fintype : Fintype ι]
  /-- The map from `ι` to objects in `C` -/
  X : ι → C

attribute [instance] Mat_.fintype

namespace Mat_

variable {C}

def Hom (M N : Mat_ C) : Type v₁ :=
  DMatrix M.ι N.ι fun i j => M.X i ⟶ N.X j

namespace Hom

open scoped Classical in

def id (M : Mat_ C) : Hom M M := fun i j => if h : i = j then eqToHom (congr_arg M.X h) else 0

def comp {M N K : Mat_ C} (f : Hom M N) (g : Hom N K) : Hom M K := fun i k =>
  ∑ j : N.ι, f i j ≫ g j k

end Hom

attribute [local simp] Hom.id Hom.comp

-- INSTANCE (free from Core): :
