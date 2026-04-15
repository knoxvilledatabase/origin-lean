/-
Extracted from CategoryTheory/Thin.lean
Genuine: 2 | Conflates: 0 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Iso

/-!
# Thin categories
A thin category (also known as a sparse category) is a category with at most one morphism between
each pair of objects.
Examples include posets, but also some indexing categories (diagrams) for special shapes of
(co)limits.
To construct a category instance one only needs to specify the `category_struct` part,
as the axioms hold for free.
If `C` is thin, then the category of functors to `C` is also thin.
Further, to show two objects are isomorphic in a thin category, it suffices only to give a morphism
in each direction.
-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁}

section

variable [CategoryStruct.{v₁} C] [Quiver.IsThin C]

def thin_category : Category C where

end

variable [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

variable [Quiver.IsThin C]

instance functor_thin : Quiver.IsThin (D ⥤ C) := fun _ _ =>
  ⟨fun α β => NatTrans.ext (by subsingleton)⟩

def iso_of_both_ways {X Y : C} (f : X ⟶ Y) (g : Y ⟶ X) :
    X ≅ Y where
  hom := f
  inv := g

instance subsingleton_iso {X Y : C} : Subsingleton (X ≅ Y) :=
  ⟨by
    intro i₁ i₂
    ext1
    subsingleton⟩

end CategoryTheory
