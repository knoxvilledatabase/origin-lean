/-
Extracted from CategoryTheory/NatTrans.lean
Genuine: 4 | Conflates: 0 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core
import Mathlib.Tactic.CategoryTheory.Reassoc

/-!
# Natural transformations

Defines natural transformations between functors.

A natural transformation `α : NatTrans F G` consists of morphisms `α.app X : F.obj X ⟶ G.obj X`,
and the naturality squares `α.naturality f : F.map f ≫ α.app Y = α.app X ≫ G.map f`,
where `f : X ⟶ Y`.

Note that we make `NatTrans.naturality` a simp lemma, with the preferred simp normal form
pushing components of natural transformations to the left.

See also `CategoryTheory.FunctorCat`, where we provide the category structure on
functors and natural transformations.

Introduces notations
* `τ.app X` for the components of natural transformations,
* `F ⟶ G` for the type of natural transformations between functors `F` and `G`
  (this and the next require `CategoryTheory.FunctorCat`),
* `σ ≫ τ` for vertical compositions, and
* `σ ◫ τ` for horizontal compositions.

-/

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

@[ext]
structure NatTrans (F G : C ⥤ D) : Type max u₁ v₂ where
  /-- The component of a natural transformation. -/
  app : ∀ X : C, F.obj X ⟶ G.obj X
  /-- The naturality square for a given morphism. -/
  naturality : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), F.map f ≫ app Y = app X ≫ G.map f := by aesop_cat

attribute [reassoc (attr := simp)] NatTrans.naturality

theorem congr_app {F G : C ⥤ D} {α β : NatTrans F G} (h : α = β) (X : C) : α.app X = β.app X := by
  aesop_cat

namespace NatTrans

protected def id (F : C ⥤ D) : NatTrans F F where app X := 𝟙 (F.obj X)

@[simp]
theorem id_app' (F : C ⥤ D) (X : C) : (NatTrans.id F).app X = 𝟙 (F.obj X) := rfl

instance (F : C ⥤ D) : Inhabited (NatTrans F F) := ⟨NatTrans.id F⟩

open Category

open CategoryTheory.Functor

section

variable {F G H : C ⥤ D}

def vcomp (α : NatTrans F G) (β : NatTrans G H) : NatTrans F H where
  app X := α.app X ≫ β.app X

theorem vcomp_app (α : NatTrans F G) (β : NatTrans G H) (X : C) :
    (vcomp α β).app X = α.app X ≫ β.app X := rfl

end

example {F G : C ⥤ D} (α : NatTrans F G) {X Y U V : C} (f : X ⟶ Y) (g : Y ⟶ U) (h : U ⟶ V) :
    α.app X ≫ G.map f ≫ G.map g ≫ G.map h = F.map f ≫ F.map g ≫ F.map h ≫ α.app V := by
  simp

end NatTrans

end CategoryTheory
