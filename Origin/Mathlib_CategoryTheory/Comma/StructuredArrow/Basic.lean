/-
Extracted from CategoryTheory/Comma/StructuredArrow/Basic.lean
Genuine: 5 of 6 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# The category of "structured arrows"

For `T : C ⥤ D`, a `T`-structured arrow with source `S : D`
is just a morphism `S ⟶ T.obj Y`, for some `Y : C`.

These form a category with morphisms `g : Y ⟶ Y'` making the obvious diagram commute.

We prove that `𝟙 (T.obj Y)` is the initial object in `T`-structured objects with source `T.obj Y`.
-/

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

def StructuredArrow (S : D) (T : C ⥤ D) :=
  Comma (Functor.fromPUnit.{0} S) T

protected def StructuredArrow.Hom {S : D} {T : C ⥤ D}
    (f g : StructuredArrow S T) : Type v₁ :=
  CommaMorphism f g

-- INSTANCE (free from Core): {S

namespace StructuredArrow

variable {S : D} {T : C ⥤ D}

abbrev right (X : StructuredArrow S T) : C := Comma.right X

abbrev hom (X : StructuredArrow S T) : S ⟶ T.obj X.right := Comma.hom X

variable {X Y : StructuredArrow S T} (f : X ⟶ Y)

abbrev Hom.right : X.right ⟶ Y.right := CommaMorphism.right f
