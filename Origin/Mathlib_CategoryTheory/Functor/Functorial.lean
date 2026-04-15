/-
Extracted from CategoryTheory/Functor/Functorial.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Unbundled functors, as a typeclass decorating the object-level function.
-/

namespace CategoryTheory

universe v v₁ v₂ v₃ u u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

class Functorial (F : C → D) : Type max v₁ v₂ u₁ u₂ where
  /-- If `F : C → D` (just a function) has `[Functorial F]`,
  we can write `map F f : F X ⟶ F Y` for the action of `F` on a morphism `f : X ⟶ Y`. -/
  map (F) : ∀ {X Y : C}, (X ⟶ Y) → (F X ⟶ F Y)
  /-- A functorial map preserves identities. -/
  map_id : ∀ {X : C}, map (𝟙 X) = 𝟙 (F X) := by cat_disch
  /-- A functorial map preserves composition of morphisms. -/
  map_comp : ∀ {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}, map (f ≫ g) = map f ≫ map g := by
    cat_disch

attribute [simp, grind =] Functorial.map_id Functorial.map_comp

export Functorial (map)

namespace Functor

def of (F : C → D) [I : Functorial.{v₁, v₂} F] : C ⥤ D :=
  { I with obj := F
           map := Functorial.map F }

end Functor

-- INSTANCE (free from Core): (F
