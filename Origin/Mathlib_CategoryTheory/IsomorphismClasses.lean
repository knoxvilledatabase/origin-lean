/-
Extracted from CategoryTheory/IsomorphismClasses.lean
Genuine: 4 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Groupoid
import Mathlib.CategoryTheory.Types

noncomputable section

/-!
# Objects of a category up to an isomorphism

`IsIsomorphic X Y := Nonempty (X ≅ Y)` is an equivalence relation on the objects of a category.
The quotient with respect to this relation defines a functor from our category to `Type`.
-/

universe v u

namespace CategoryTheory

section Category

variable {C : Type u} [Category.{v} C]

def IsIsomorphic : C → C → Prop := fun X Y => Nonempty (X ≅ Y)

variable (C)

def isIsomorphicSetoid : Setoid C where
  r := IsIsomorphic
  iseqv := ⟨fun X => ⟨Iso.refl X⟩, fun ⟨α⟩ => ⟨α.symm⟩, fun ⟨α⟩ ⟨β⟩ => ⟨α.trans β⟩⟩

end Category

def isomorphismClasses : Cat.{v, u} ⥤ Type u where
  obj C := Quotient (isIsomorphicSetoid C.α)
  map {_ _} F := Quot.map F.obj fun _ _ ⟨f⟩ => ⟨F.mapIso f⟩
  map_id {C} := by  -- Porting note: this used to be `tidy`
    dsimp; apply funext; intro x
    apply @Quot.recOn _ _ _ x
    · intro _ _ p
      simp only [types_id_apply]
    · intro _
      rfl
  map_comp {C D E} f g := by -- Porting note(s): idem
    dsimp; apply funext; intro x
    apply @Quot.recOn _ _ _ x
    · intro _ _ _
      simp only [types_id_apply]
    · intro _
      rfl

theorem Groupoid.isIsomorphic_iff_nonempty_hom {C : Type u} [Groupoid.{v} C] {X Y : C} :
    IsIsomorphic X Y ↔ Nonempty (X ⟶ Y) :=
  (Groupoid.isoEquivHom X Y).nonempty_congr

end CategoryTheory
