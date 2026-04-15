/-
Extracted from CategoryTheory/Preadditive/Injective/Preserves.lean
Genuine: 4 of 7 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Preservation of injective objects

We define a typeclass `Functor.PreservesInjectiveObjects`.

We restate the existing result that if `F ⊣ G` is an adjunction and `F` preserves monomorphisms,
then `G` preserves injective objects. We show that the converse is true if the codomain of `F` has
enough injectives.
-/

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]

class Functor.PreservesInjectiveObjects (F : C ⥤ D) : Prop where
  injective_obj {X : C} : Injective X → Injective (F.obj X)

-- INSTANCE (free from Core): Functor.injective_obj

theorem Functor.injective_obj_of_injective (F : C ⥤ D) [F.PreservesInjectiveObjects] {X : C}
    (h : Injective X) : Injective (F.obj X) :=
  Functor.PreservesInjectiveObjects.injective_obj h

-- INSTANCE (free from Core): Functor.preservesInjectiveObjects_comp

theorem Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.PreservesMonomorphisms] :
    G.PreservesInjectiveObjects where
  injective_obj h := adj.map_injective _ h

-- INSTANCE (free from Core): (priority

set_option backward.isDefEq.respectTransparency false in

theorem Functor.preservesMonomorphisms_of_adjunction_of_preservesInjectiveObjects
    [EnoughInjectives D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [G.PreservesInjectiveObjects] :
    F.PreservesMonomorphisms where
  preserves {X Y} f _ := by
    suffices ∃ h, F.map f ≫ h = Injective.ι (F.obj X) from mono_of_mono_fac this.choose_spec
    exact ⟨F.map (Injective.factorThru (adj.unit.app X ≫ G.map (Injective.ι _)) f) ≫
      adj.counit.app (Injective.under (F.obj X)), by simp [← Functor.map_comp_assoc]⟩

end CategoryTheory
