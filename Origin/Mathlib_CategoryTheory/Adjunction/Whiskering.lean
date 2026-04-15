/-
Extracted from CategoryTheory/Adjunction/Whiskering.lean
Genuine: 2 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.Adjunction.Basic

/-!

Given categories `C D E`, functors `F : D ⥤ E` and `G : E ⥤ D` with an adjunction
`F ⊣ G`, we provide the induced adjunction between the functor categories `C ⥤ D` and `C ⥤ E`,
and the functor categories `E ⥤ C` and `D ⥤ C`.

-/

namespace CategoryTheory.Adjunction

open CategoryTheory

variable (C : Type*) {D E : Type*} [Category C] [Category D] [Category E] {F : D ⥤ E} {G : E ⥤ D}

@[simps! unit_app_app counit_app_app]
protected def whiskerRight (adj : F ⊣ G) :
    (whiskeringRight C D E).obj F ⊣ (whiskeringRight C E D).obj G where
  unit :=
    { app := fun X =>
        (Functor.rightUnitor _).inv ≫ whiskerLeft X adj.unit ≫ (Functor.associator _ _ _).inv
      naturality := by intros; ext; dsimp; simp }
  counit :=
    { app := fun X =>
        (Functor.associator _ _ _).hom ≫ whiskerLeft X adj.counit ≫ (Functor.rightUnitor _).hom
      naturality := by intros; ext; dsimp; simp }

@[simps! unit_app_app counit_app_app]
protected def whiskerLeft (adj : F ⊣ G) :
    (whiskeringLeft E D C).obj G ⊣ (whiskeringLeft D E C).obj F where
  unit :=
    { app := fun X =>
        (Functor.leftUnitor _).inv ≫ whiskerRight adj.unit X ≫ (Functor.associator _ _ _).hom }
  counit :=
    { app := fun X =>
        (Functor.associator _ _ _).inv ≫ whiskerRight adj.counit X ≫ (Functor.leftUnitor _).hom }
  left_triangle_components X := by ext; simp [← X.map_comp]
  right_triangle_components X := by ext; simp [← X.map_comp]

end CategoryTheory.Adjunction
