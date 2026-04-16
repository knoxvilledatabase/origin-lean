/-
Extracted from CategoryTheory/Functor/Basic.lean
Genuine: 7 | Conflates: 0 | Dissolved: 0 | Infrastructure: 5
-/
import Origin.Core
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Combinatorics.Quiver.Prefunctor

noncomputable section

/-!
# Functors

Defines a functor between categories, extending a `Prefunctor` between quivers.

Introduces, in the `CategoryTheory` scope, notations `C ⥤ D` for the type of all functors
from `C` to `D`, `𝟭` for the identity functor and `⋙` for functor composition.

TODO: Switch to using the `⇒` arrow.
-/

namespace CategoryTheory

universe v v₁ v₂ v₃ u u₁ u₂ u₃

section

structure Functor (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D]
    extends Prefunctor C D : Type max v₁ v₂ u₁ u₂ where
  /-- A functor preserves identity morphisms. -/
  map_id : ∀ X : C, map (𝟙 X) = 𝟙 (obj X) := by aesop_cat
  /-- A functor preserves composition. -/
  map_comp : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), map (f ≫ g) = map f ≫ map g := by aesop_cat

end

scoped [CategoryTheory] infixr:26 " ⥤ " => Functor -- type as \func

attribute [simp] Functor.map_id Functor.map_comp

lemma Functor.map_comp_assoc {C : Type u₁} [Category C] {D : Type u₂} [Category D] (F : C ⥤ D)
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) {W : D} (h : F.obj Z ⟶ W) :
    (F.map (f ≫ g)) ≫ h = F.map f ≫ F.map g ≫ h := by
  rw [F.map_comp, Category.assoc]

namespace Functor

section

variable (C : Type u₁) [Category.{v₁} C]

initialize_simps_projections Functor

protected def id : C ⥤ C where
  obj X := X
  map f := f

scoped [CategoryTheory] notation "𝟭" => Functor.id -- Type this as `\sb1`

instance : Inhabited (C ⥤ C) :=
  ⟨Functor.id C⟩

variable {C}

@[simp]
theorem id_obj (X : C) : (𝟭 C).obj X = X := rfl

@[simp]
theorem id_map {X Y : C} (f : X ⟶ Y) : (𝟭 C).map f = f := rfl

end

section

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]

@[simps obj]
def comp (F : C ⥤ D) (G : D ⥤ E) : C ⥤ E where
  obj X := G.obj (F.obj X)
  map f := G.map (F.map f)
  map_comp := by intros; dsimp; rw [F.map_comp, G.map_comp]

scoped [CategoryTheory] infixr:80 " ⋙ " => Functor.comp

@[simp]
theorem comp_map (F : C ⥤ D) (G : D ⥤ E) {X Y : C} (f : X ⟶ Y) :
    (F ⋙ G).map f = G.map (F.map f) := rfl

protected theorem comp_id (F : C ⥤ D) : F ⋙ 𝟭 D = F := by cases F; rfl

protected theorem id_comp (F : C ⥤ D) : 𝟭 C ⋙ F = F := by cases F; rfl

@[simp]
theorem map_dite (F : C ⥤ D) {X Y : C} {P : Prop} [Decidable P]
    (f : P → (X ⟶ Y)) (g : ¬P → (X ⟶ Y)) :
    F.map (if h : P then f h else g h) = if h : P then F.map (f h) else F.map (g h) := by
  aesop_cat

@[simp]
theorem toPrefunctor_comp (F : C ⥤ D) (G : D ⥤ E) :
    F.toPrefunctor.comp G.toPrefunctor = (F ⋙ G).toPrefunctor := rfl

end

end Functor

end CategoryTheory
