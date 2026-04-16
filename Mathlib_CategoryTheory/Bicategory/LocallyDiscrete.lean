/-
Extracted from CategoryTheory/Bicategory/LocallyDiscrete.lean
Genuine: 7 | Conflates: 0 | Dissolved: 0 | Infrastructure: 14
-/
import Origin.Core
import Mathlib.CategoryTheory.DiscreteCategory
import Mathlib.CategoryTheory.Bicategory.Functor.Prelax
import Mathlib.CategoryTheory.Bicategory.Strict

noncomputable section

/-!
# Locally discrete bicategories

A category `C` can be promoted to a strict bicategory `LocallyDiscrete C`. The objects and the
1-morphisms in `LocallyDiscrete C` are the same as the objects and the morphisms, respectively,
in `C`, and the 2-morphisms in `LocallyDiscrete C` are the equalities between 1-morphisms. In
other words, the category consisting of the 1-morphisms between each pair of objects `X` and `Y`
in `LocallyDiscrete C` is defined as the discrete category associated with the type `X ⟶ Y`.
-/

namespace CategoryTheory

open Bicategory Discrete

universe w₂ w₁ v₂ v₁ v u₂ u₁ u

section

variable {C : Type u}

@[ext]
structure LocallyDiscrete (C : Type u) where
  /-- A wrapper for promoting any category to a bicategory,
  with the only 2-morphisms being equalities.
  -/
  as : C

namespace LocallyDiscrete

@[simp]
theorem mk_as (a : LocallyDiscrete C) : mk a.as = a := rfl

@[simps]
def locallyDiscreteEquiv : LocallyDiscrete C ≃ C where
  toFun := LocallyDiscrete.as
  invFun := LocallyDiscrete.mk
  left_inv := by aesop_cat
  right_inv := by aesop_cat

instance [DecidableEq C] : DecidableEq (LocallyDiscrete C) :=
  locallyDiscreteEquiv.decidableEq

instance [Inhabited C] : Inhabited (LocallyDiscrete C) :=
  ⟨⟨default⟩⟩

instance categoryStruct [CategoryStruct.{v} C] : CategoryStruct (LocallyDiscrete C) where
  Hom a b := Discrete (a.as ⟶ b.as)
  id a := ⟨𝟙 a.as⟩
  comp f g := ⟨f.as ≫ g.as⟩

variable [CategoryStruct.{v} C]

@[simp]
lemma id_as (a : LocallyDiscrete C) : (𝟙 a : Discrete (a.as ⟶ a.as)).as = 𝟙 a.as :=
  rfl

@[simp]
lemma comp_as {a b c : LocallyDiscrete C} (f : a ⟶ b) (g : b ⟶ c) : (f ≫ g).as = f.as ≫ g.as :=
  rfl

instance (priority := 900) homSmallCategory (a b : LocallyDiscrete C) : SmallCategory (a ⟶ b) :=
  CategoryTheory.discreteCategory (a.as ⟶ b.as)

instance subsingleton2Hom {a b : LocallyDiscrete C} (f g : a ⟶ b) : Subsingleton (f ⟶ g) :=
  instSubsingletonDiscreteHom f g

theorem eq_of_hom {X Y : LocallyDiscrete C} {f g : X ⟶ Y} (η : f ⟶ g) : f = g :=
  Discrete.ext η.1.1

end LocallyDiscrete

variable (C)

variable [Category.{v} C]

instance locallyDiscreteBicategory : Bicategory (LocallyDiscrete C) where
  whiskerLeft _ _ _ η := eqToHom (congr_arg₂ (· ≫ ·) rfl (LocallyDiscrete.eq_of_hom η))
  whiskerRight η _ := eqToHom (congr_arg₂ (· ≫ ·) (LocallyDiscrete.eq_of_hom η) rfl)
  associator f g h := eqToIso <| by apply Discrete.ext; simp
  leftUnitor f := eqToIso <| by apply Discrete.ext; simp
  rightUnitor f := eqToIso <| by apply Discrete.ext; simp

instance locallyDiscreteBicategory.strict : Strict (LocallyDiscrete C) where
  id_comp _ := Discrete.ext (Category.id_comp _)
  comp_id _ := Discrete.ext (Category.comp_id _)
  assoc _ _ _ := Discrete.ext (Category.assoc _ _ _)

end

section

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]

@[simp]
lemma PrelaxFunctor.map₂_eqToHom (F : PrelaxFunctor B C) {a b : B} {f g : a ⟶ b} (h : f = g) :
    F.map₂ (eqToHom h) = eqToHom (F.congr_map h) := by
  subst h; simp only [eqToHom_refl, PrelaxFunctor.map₂_id]

end

namespace Bicategory

abbrev IsLocallyDiscrete (B : Type*) [Bicategory B] := ∀ (b c : B), IsDiscrete (b ⟶ c)

instance (C : Type*) [Category C] : IsLocallyDiscrete (LocallyDiscrete C) :=
  fun _ _ ↦ Discrete.isDiscrete _

instance (B : Type*) [Bicategory B] [IsLocallyDiscrete B] : Strict B where
  id_comp f := obj_ext_of_isDiscrete (leftUnitor f).hom
  comp_id f := obj_ext_of_isDiscrete (rightUnitor f).hom
  assoc f g h := obj_ext_of_isDiscrete (associator f g h).hom

end Bicategory

end CategoryTheory

section

open CategoryTheory LocallyDiscrete

universe v u

namespace Quiver.Hom

variable {C : Type u} [CategoryStruct.{v} C]

@[simps]
def toLoc {a b : C} (f : a ⟶ b) : LocallyDiscrete.mk a ⟶ LocallyDiscrete.mk b :=
  ⟨f⟩

@[simp]
lemma id_toLoc (a : C) : (𝟙 a).toLoc = 𝟙 (LocallyDiscrete.mk a) :=
  rfl

@[simp]
lemma comp_toLoc {a b c : C} (f : a ⟶ b) (g : b ⟶ c) : (f ≫ g).toLoc = f.toLoc ≫ g.toLoc :=
  rfl

end Quiver.Hom

@[simp]
lemma CategoryTheory.LocallyDiscrete.eqToHom_toLoc {C : Type u} [Category.{v} C] {a b : C}
    (h : a = b) : (eqToHom h).toLoc = eqToHom (congrArg LocallyDiscrete.mk h) := by
  subst h; rfl

end
