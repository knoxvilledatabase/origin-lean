/-
Extracted from CategoryTheory/Subobject/FactorThru.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Factoring through subobjects

The predicate `h : P.Factors f`, for `P : Subobject Y` and `f : X ⟶ Y`
asserts the existence of some `P.factorThru f : X ⟶ (P : C)` making the obvious diagram commute.

-/

universe v₁ v₂ u₁ u₂

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C] {X Y Z : C}

variable {D : Type u₂} [Category.{v₂} D]

namespace CategoryTheory

namespace MonoOver

def Factors {X Y : C} (P : MonoOver Y) (f : X ⟶ Y) : Prop :=
  ∃ g : X ⟶ (P : C), g ≫ P.arrow = f

set_option backward.isDefEq.respectTransparency false in

theorem factors_congr {X : C} {f g : MonoOver X} {Y : C} (h : Y ⟶ X) (e : f ≅ g) :
    f.Factors h ↔ g.Factors h :=
  ⟨fun ⟨u, hu⟩ => ⟨u ≫ ((MonoOver.forget _).map e.hom).left, by simp [hu]⟩, fun ⟨u, hu⟩ =>
    ⟨u ≫ ((MonoOver.forget _).map e.inv).left, by simp [hu]⟩⟩

def factorThru {X Y : C} (P : MonoOver Y) (f : X ⟶ Y) (h : Factors P f) : X ⟶ (P : C) :=
  Classical.choose h

end MonoOver

namespace Subobject

set_option backward.isDefEq.respectTransparency false in

def Factors {X Y : C} (P : Subobject Y) (f : X ⟶ Y) : Prop :=
  Quotient.liftOn' P (fun P => P.Factors f)
    (by
      rintro P Q ⟨h⟩
      apply propext
      constructor
      · rintro ⟨i, w⟩
        exact ⟨i ≫ h.hom.hom.left, by rw [Category.assoc, Over.w h.hom.hom, w]⟩
      · rintro ⟨i, w⟩
        exact ⟨i ≫ h.inv.hom.left, by rw [Category.assoc, Over.w h.inv.hom, w]⟩)
