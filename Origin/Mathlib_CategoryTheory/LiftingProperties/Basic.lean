/-
Extracted from CategoryTheory/LiftingProperties/Basic.lean
Genuine: 14 of 20 | Dissolved: 0 | Infrastructure: 6
-/
import Origin.Core

/-!
# Lifting properties

This file defines the lifting property of two morphisms in a category and
shows basic properties of this notion.

## Main results
- `HasLiftingProperty`: the definition of the lifting property

## Tags
lifting property

## TODO
1) direct/inverse images, adjunctions

-/

universe v

namespace CategoryTheory

open Category

variable {C : Type*} [Category* C] {A B B' X Y Y' : C} (i : A ⟶ B) (i' : B ⟶ B') (p : X ⟶ Y)
  (p' : Y ⟶ Y')

class HasLiftingProperty : Prop where
  /-- Unique field expressing that any commutative square built from `f` and `g` has a lift -/
  sq_hasLift : ∀ {f : A ⟶ X} {g : B ⟶ Y} (sq : CommSq f i p g), sq.HasLift

-- INSTANCE (free from Core): (priority

namespace HasLiftingProperty

variable {i p}

theorem op (h : HasLiftingProperty i p) : HasLiftingProperty p.op i.op :=
  ⟨fun {f} {g} sq => by
    simp only [CommSq.HasLift.iff_unop, Quiver.Hom.unop_op]
    infer_instance⟩

theorem unop {A B X Y : Cᵒᵖ} {i : A ⟶ B} {p : X ⟶ Y} (h : HasLiftingProperty i p) :
    HasLiftingProperty p.unop i.unop :=
  ⟨fun {f} {g} sq => by
    rw [CommSq.HasLift.iff_op]
    simp only [Quiver.Hom.op_unop]
    infer_instance⟩

theorem iff_op : HasLiftingProperty i p ↔ HasLiftingProperty p.op i.op :=
  ⟨op, unop⟩

theorem iff_unop {A B X Y : Cᵒᵖ} (i : A ⟶ B) (p : X ⟶ Y) :
    HasLiftingProperty i p ↔ HasLiftingProperty p.unop i.unop :=
  ⟨unop, op⟩

variable (i p)

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): of_comp_left

-- INSTANCE (free from Core): of_comp_right

set_option backward.isDefEq.respectTransparency false in

theorem of_arrow_iso_left {A B A' B' X Y : C} {i : A ⟶ B} {i' : A' ⟶ B'}
    (e : Arrow.mk i ≅ Arrow.mk i') (p : X ⟶ Y) [hip : HasLiftingProperty i p] :
    HasLiftingProperty i' p := by
  rw [Arrow.iso_w' e]
  infer_instance

set_option backward.isDefEq.respectTransparency false in

theorem of_arrow_iso_right {A B X Y X' Y' : C} (i : A ⟶ B) {p : X ⟶ Y} {p' : X' ⟶ Y'}
    (e : Arrow.mk p ≅ Arrow.mk p') [hip : HasLiftingProperty i p] : HasLiftingProperty i p' := by
  rw [Arrow.iso_w' e]
  infer_instance

theorem iff_of_arrow_iso_left {A B A' B' X Y : C} {i : A ⟶ B} {i' : A' ⟶ B'}
    (e : Arrow.mk i ≅ Arrow.mk i') (p : X ⟶ Y) :
    HasLiftingProperty i p ↔ HasLiftingProperty i' p := by
  constructor <;> intro
  exacts [of_arrow_iso_left e p, of_arrow_iso_left e.symm p]

theorem iff_of_arrow_iso_right {A B X Y X' Y' : C} (i : A ⟶ B) {p : X ⟶ Y} {p' : X' ⟶ Y'}
    (e : Arrow.mk p ≅ Arrow.mk p') : HasLiftingProperty i p ↔ HasLiftingProperty i p' := by
  constructor <;> intro
  exacts [of_arrow_iso_right i e, of_arrow_iso_right i e.symm]

end HasLiftingProperty

set_option backward.isDefEq.respectTransparency false in

set_option backward.isDefEq.respectTransparency false in

lemma RetractArrow.rightLiftingProperty
    {X Y Z W X' Y' : C} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (h : RetractArrow f' f) (g : Z ⟶ W) [HasLiftingProperty g f] : HasLiftingProperty g f' where
  sq_hasLift := fun {u v} sq ↦
    have sq' : CommSq (u ≫ h.i.left) g f (v ≫ h.i.right) :=
      ⟨by rw [← Category.assoc, ← sq.w, Category.assoc, RetractArrow.i_w, Category.assoc]⟩
    ⟨⟨{ l := sq'.lift ≫ h.r.left}⟩⟩

namespace Arrow

abbrev LiftStruct {f g : Arrow C} (φ : f ⟶ g) := (CommSq.mk φ.w).LiftStruct

set_option backward.isDefEq.respectTransparency false in

lemma hasLiftingProperty_iff {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y) :
    HasLiftingProperty i p ↔
      ∀ (φ : Arrow.mk i ⟶ Arrow.mk p), Nonempty (LiftStruct φ) := by
  constructor
  · intro _ φ
    have sq : CommSq φ.left i p φ.right := CommSq.mk φ.w
    exact ⟨{ l := sq.lift }⟩
  · intro h
    exact ⟨fun {f g} sq ↦ ⟨h (Arrow.homMk f g sq.w)⟩⟩

end Arrow

def HasLiftingPropertyFixedTop (t : A ⟶ X) : Prop :=
  ∀ (b : B ⟶ Y) (sq : CommSq t i p b), sq.HasLift

def HasLiftingPropertyFixedBot (b : B ⟶ Y) : Prop :=
  ∀ (t : A ⟶ X) (sq : CommSq t i p b), sq.HasLift

end CategoryTheory
