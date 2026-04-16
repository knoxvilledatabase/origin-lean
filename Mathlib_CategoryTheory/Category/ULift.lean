/-
Extracted from CategoryTheory/Category/ULift.lean
Genuine: 15 | Conflates: 0 | Dissolved: 0 | Infrastructure: 7
-/
import Origin.Core
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.EqToHom
import Mathlib.Data.ULift

noncomputable section

/-!
# Basic API for ULift

This file contains a very basic API for working with the categorical
instance on `ULift C` where `C` is a type with a category instance.

1. `CategoryTheory.ULift.upFunctor` is the functorial version of the usual `ULift.up`.
2. `CategoryTheory.ULift.downFunctor` is the functorial version of the usual `ULift.down`.
3. `CategoryTheory.ULift.equivalence` is the categorical equivalence between
  `C` and `ULift C`.

# ULiftHom

Given a type `C : Type u`, `ULiftHom.{w} C` is just an alias for `C`.
If we have `category.{v} C`, then `ULiftHom.{w} C` is endowed with a category instance
whose morphisms are obtained by applying `ULift.{w}` to the morphisms from `C`.

This is a category equivalent to `C`. The forward direction of the equivalence is `ULiftHom.up`,
the backward direction is `ULiftHom.down` and the equivalence is `ULiftHom.equiv`.

# AsSmall

This file also contains a construction which takes a type `C : Type u` with a
category instance `Category.{v} C` and makes a small category
`AsSmall.{w} C : Type (max w v u)` equivalent to `C`.

The forward direction of the equivalence, `C ⥤ AsSmall C`, is denoted `AsSmall.up`
and the backward direction is `AsSmall.down`. The equivalence itself is `AsSmall.equiv`.
-/

universe w₁ v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]

@[simps]
def ULift.upFunctor : C ⥤ ULift.{u₂} C where
  obj := ULift.up
  map f := f

@[simps]
def ULift.downFunctor : ULift.{u₂} C ⥤ C where
  obj := ULift.down
  map f := f

@[simps]
def ULift.equivalence : C ≌ ULift.{u₂} C where
  functor := ULift.upFunctor
  inverse := ULift.downFunctor
  unitIso :=
    { hom := 𝟙 _
      inv := 𝟙 _ }
  counitIso :=
    { hom :=
        { app := fun _ => 𝟙 _
          naturality := fun X Y f => by
            change f ≫ 𝟙 _ = 𝟙 _ ≫ f
            simp }
      inv :=
        { app := fun _ => 𝟙 _
          naturality := fun X Y f => by
            change f ≫ 𝟙 _ = 𝟙 _ ≫ f
            simp }
      hom_inv_id := by
        ext
        change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
        simp
      inv_hom_id := by
        ext
        change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
        simp }
  functor_unitIso_comp X := by
    change 𝟙 X ≫ 𝟙 X = 𝟙 X
    simp

section ULiftHom

def ULiftHom.{w,u} (C : Type u) : Type u :=
  let _ := ULift.{w} C
  C

instance {C} [Inhabited C] : Inhabited (ULiftHom C) :=
  ⟨(default : C)⟩

def ULiftHom.objDown {C} (A : ULiftHom C) : C :=
  A

def ULiftHom.objUp {C} (A : C) : ULiftHom C :=
  A

@[simp]
theorem objDown_objUp {C} (A : C) : (ULiftHom.objUp A).objDown = A :=
  rfl

@[simp]
theorem objUp_objDown {C} (A : ULiftHom C) : ULiftHom.objUp A.objDown = A :=
  rfl

instance ULiftHom.category : Category.{max v₂ v₁} (ULiftHom.{v₂} C) where
  Hom A B := ULift.{v₂} <| A.objDown ⟶ B.objDown
  id _ := ⟨𝟙 _⟩
  comp f g := ⟨f.down ≫ g.down⟩

@[simps]
def ULiftHom.up : C ⥤ ULiftHom C where
  obj := ULiftHom.objUp
  map f := ⟨f⟩

@[simps]
def ULiftHom.down : ULiftHom C ⥤ C where
  obj := ULiftHom.objDown
  map f := f.down

def ULiftHom.equiv : C ≌ ULiftHom C where
  functor := ULiftHom.up
  inverse := ULiftHom.down
  unitIso := NatIso.ofComponents fun _ => eqToIso rfl
  counitIso := NatIso.ofComponents fun _ => eqToIso rfl

end ULiftHom

@[nolint unusedArguments]
def AsSmall.{w, v, u} (D : Type u) [Category.{v} D] := ULift.{max w v} D

instance : SmallCategory (AsSmall.{w₁} C) where
  Hom X Y := ULift.{max w₁ u₁} <| X.down ⟶ Y.down
  id _ := ⟨𝟙 _⟩
  comp f g := ⟨f.down ≫ g.down⟩

@[simps]
def AsSmall.up : C ⥤ AsSmall C where
  obj X := ⟨X⟩
  map f := ⟨f⟩

@[simps]
def AsSmall.down : AsSmall C ⥤ C where
  obj X := ULift.down X
  map f := f.down

@[simp]
theorem eqToHom_down {X Y : AsSmall C} (h : X = Y) :
    (eqToHom h).down = eqToHom (congrArg ULift.down h) := by
  subst h
  rfl

@[simps]
def AsSmall.equiv : C ≌ AsSmall C where
  functor := AsSmall.up
  inverse := AsSmall.down
  unitIso := NatIso.ofComponents fun _ => eqToIso rfl
  counitIso := NatIso.ofComponents fun _ => eqToIso <| ULift.ext _ _ rfl

instance [Inhabited C] : Inhabited (AsSmall C) :=
  ⟨⟨default⟩⟩

def ULiftHomULiftCategory.equiv.{v', u', v, u} (C : Type u) [Category.{v} C] :
    C ≌ ULiftHom.{v'} (ULift.{u'} C) :=
  ULift.equivalence.trans ULiftHom.equiv

end CategoryTheory
