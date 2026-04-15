/-
Extracted from CategoryTheory/Monoidal/Subcategory.lean
Genuine: 2 of 23 | Dissolved: 0 | Infrastructure: 21
-/
import Origin.Core
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.CategoryTheory.Monoidal.Transport
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.CategoryTheory.Closed.Monoidal

/-!
# Full monoidal subcategories

Given a monoidal category `C` and a monoidal predicate on `C`, that is a function `P : C → Prop`
closed under `𝟙_` and `⊗`, we can put a monoidal structure on `{X : C // P X}` (the category
structure is defined in `Mathlib.CategoryTheory.FullSubcategory`).

When `C` is also braided/symmetric, the full monoidal subcategory also inherits the
braided/symmetric structure.

## TODO
* Add monoidal/braided versions of `CategoryTheory.FullSubcategory.Lift`
-/

universe u v

namespace CategoryTheory

namespace MonoidalCategory

open Iso

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] (P : C → Prop)

class MonoidalPredicate : Prop where
  prop_id : P (𝟙_ C) := by aesop_cat
  prop_tensor : ∀ {X Y}, P X → P Y → P (X ⊗ Y) := by aesop_cat

open MonoidalPredicate

variable [MonoidalPredicate P]

@[simps]
instance : MonoidalCategoryStruct (FullSubcategory P) where
  tensorObj X Y := ⟨X.1 ⊗ Y.1, prop_tensor X.2 Y.2⟩
  whiskerLeft X _ _ f := X.1 ◁ f
  whiskerRight {X₁ X₂} (f : X₁.1 ⟶ X₂.1) Y := (f ▷ Y.1 :)
  tensorHom f g := f ⊗ g
  tensorUnit := ⟨𝟙_ C, prop_id⟩
  associator X Y Z :=
    ⟨(α_ X.1 Y.1 Z.1).hom, (α_ X.1 Y.1 Z.1).inv, hom_inv_id (α_ X.1 Y.1 Z.1),
      inv_hom_id (α_ X.1 Y.1 Z.1)⟩
  leftUnitor X := ⟨(λ_ X.1).hom, (λ_ X.1).inv, hom_inv_id (λ_ X.1), inv_hom_id (λ_ X.1)⟩
  rightUnitor X := ⟨(ρ_ X.1).hom, (ρ_ X.1).inv, hom_inv_id (ρ_ X.1), inv_hom_id (ρ_ X.1)⟩

instance fullMonoidalSubcategory : MonoidalCategory (FullSubcategory P) :=
  Monoidal.induced (fullSubcategoryInclusion P)
    { μIso := fun _ _ => eqToIso rfl
      εIso := eqToIso rfl }

instance fullSubcategoryInclusionMonoidal : (fullSubcategoryInclusion P).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun _ _ ↦ Iso.refl _ }

open Functor.LaxMonoidal Functor.OplaxMonoidal

@[simp] lemma fullSubcategoryInclusion_ε : ε (fullSubcategoryInclusion P) = 𝟙 _ := rfl

@[simp] lemma fullSubcategoryInclusion_η : ε (fullSubcategoryInclusion P) = 𝟙 _ := rfl

@[simp] lemma fullSubcategoryInclusion_μ (X Y : FullSubcategory P) :
    μ (fullSubcategoryInclusion P) X Y = 𝟙 _ := rfl

@[simp] lemma fullSubcategoryInclusion_δ (X Y : FullSubcategory P) :
    δ (fullSubcategoryInclusion P) X Y = 𝟙 _ := rfl

section

variable [Preadditive C]

instance [MonoidalPreadditive C] : MonoidalPreadditive (FullSubcategory P) :=
  monoidalPreadditive_of_faithful (fullSubcategoryInclusion P)

variable (R : Type*) [Ring R] [Linear R C]

instance [MonoidalPreadditive C] [MonoidalLinear R C] : MonoidalLinear R (FullSubcategory P) :=
  monoidalLinearOfFaithful R (fullSubcategoryInclusion P)

end

section

variable {P} {P' : C → Prop} [MonoidalPredicate P'] (h : ∀ ⦃X⦄, P X → P' X)

instance  : (FullSubcategory.map h).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun _ _ ↦ Iso.refl _ }

@[simp] lemma fullSubcategory_map_ε : ε (FullSubcategory.map h) = 𝟙 _ := rfl

@[simp] lemma fullSubcategory_map_η : η (FullSubcategory.map h) = 𝟙 _ := rfl

@[simp] lemma fullSubcategory_map_μ (X Y : FullSubcategory P) :
    μ (FullSubcategory.map h) X Y = 𝟙 _ := rfl

@[simp] lemma fullSubcategory_map_δ (X Y : FullSubcategory P) :
    δ (FullSubcategory.map h) X Y = 𝟙 _ := rfl

end

section Braided

variable [BraidedCategory C]

instance fullBraidedSubcategory : BraidedCategory (FullSubcategory P) :=
  braidedCategoryOfFaithful (fullSubcategoryInclusion P)
    (fun X Y =>
      ⟨(β_ X.1 Y.1).hom, (β_ X.1 Y.1).inv, (β_ X.1 Y.1).hom_inv_id, (β_ X.1 Y.1).inv_hom_id⟩)
    fun X Y => by aesop_cat

instance : (fullSubcategoryInclusion P).Braided where

variable {P}

instance {P' : C → Prop} [MonoidalPredicate P'] (h : ∀ ⦃X⦄, P X → P' X) :
    (FullSubcategory.map h).Braided where

end Braided

section Symmetric

variable [SymmetricCategory C]

instance fullSymmetricSubcategory : SymmetricCategory (FullSubcategory P) :=
  symmetricCategoryOfFaithful (fullSubcategoryInclusion P)

end Symmetric

section Closed

variable [MonoidalClosed C]

class ClosedPredicate : Prop where
  prop_ihom : ∀ {X Y}, P X → P Y → P ((ihom X).obj Y) := by aesop_cat

open ClosedPredicate

variable [ClosedPredicate P]

instance fullMonoidalClosedSubcategory : MonoidalClosed (FullSubcategory P) where
  closed X :=
    { rightAdj := FullSubcategory.lift P (fullSubcategoryInclusion P ⋙ ihom X.1)
        fun Y => prop_ihom X.2 Y.2
      adj :=
        { unit :=
          { app := fun Y => (ihom.coev X.1).app Y.1
            naturality := fun _ _ f => ihom.coev_naturality X.1 f }
          counit :=
          { app := fun Y => (ihom.ev X.1).app Y.1
            naturality := fun _ _ f => ihom.ev_naturality X.1 f }
          left_triangle_components := fun X ↦
            by simp [FullSubcategory.comp_def, FullSubcategory.id_def]
          right_triangle_components := fun Y ↦
            by simp [FullSubcategory.comp_def, FullSubcategory.id_def] } }

@[simp]
theorem fullMonoidalClosedSubcategory_ihom_obj (X Y : FullSubcategory P) :
    ((ihom X).obj Y).obj = (ihom X.obj).obj Y.obj :=
  rfl

@[simp]
theorem fullMonoidalClosedSubcategory_ihom_map (X : FullSubcategory P) {Y Z : FullSubcategory P}
    (f : Y ⟶ Z) : (ihom X).map f = (ihom X.obj).map f :=
  rfl

end Closed

end MonoidalCategory

end CategoryTheory
