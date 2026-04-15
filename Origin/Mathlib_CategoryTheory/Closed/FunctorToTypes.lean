/-
Extracted from CategoryTheory/Closed/FunctorToTypes.lean
Genuine: 4 | Conflates: 0 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core
import Mathlib.CategoryTheory.Functor.FunctorHom
import Mathlib.CategoryTheory.Closed.Monoidal

/-!
# Functors to Type are closed.

Show that `C ⥤ Type max w v u` is monoidal closed for `C` a category in `Type u` with morphisms in
`Type v`, and `w` an arbitrary universe.

## TODO
It should be shown that `C ⥤ Type max w v u` is cartesian closed.

-/

universe w v' v u u'

open CategoryTheory Functor MonoidalCategory

namespace CategoryTheory.FunctorToTypes

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

variable (F : C ⥤ Type max w v u)

@[simps!]
def functorHomEquiv (G H : C ⥤ Type max w v u) : (G ⟶ F.functorHom H) ≃ (F ⊗ G ⟶ H) :=
  (Functor.functorHomEquiv F H G).trans (homObjEquiv F H G)

@[simps]
def rightAdj_map {F G H : C ⥤ Type max w v u} (f : G ⟶ H) (c : C) (a : (F.functorHom G).obj c) :
    (F.functorHom H).obj c where
  app d b := a.app d b ≫ f.app d
  naturality g h := by
    have := a.naturality g h
    change (F.map g ≫ a.app _ (h ≫ g)) ≫ _ = _
    aesop

@[simps!]
def rightAdj : (C ⥤ Type max w v u) ⥤ C ⥤ Type max w v u where
  obj G := F.functorHom G
  map f := { app := rightAdj_map f }

def adj : tensorLeft F ⊣ rightAdj F where
  unit := {
    app := fun G ↦ (functorHomEquiv F G _).2 (𝟙 _)
    naturality := fun G H f ↦ by
      dsimp [rightAdj]
      ext _
      simp [FunctorToTypes.naturality] }
  counit := { app := fun G ↦ functorHomEquiv F _ G (𝟙 _) }

instance closed : Closed F where
  adj := adj F

instance monoidalClosed : MonoidalClosed (C ⥤ Type max w v u) where

end CategoryTheory.FunctorToTypes
