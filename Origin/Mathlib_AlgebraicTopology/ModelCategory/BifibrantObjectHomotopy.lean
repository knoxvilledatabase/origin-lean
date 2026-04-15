/-
Extracted from AlgebraicTopology/ModelCategory/BifibrantObjectHomotopy.lean
Genuine: 9 of 18 | Dissolved: 0 | Infrastructure: 9
-/
import Origin.Core

/-!
# The homotopy category of bifibrant objects

We construct the homotopy category `BifibrantObject.HoCat C` of bifibrant
objects in a model category `C` and show that the functor
`BifibrantObject.toHoCat : BifibrantObject C ⥤ BifibrantObject.HoCat C`
is a localization functor with respect to weak equivalences.
We also show that certain localizer morphisms are localized weak equivalences,
which can be understood by saying that we obtain the same localized
category (up to equivalence) by inverting weak equivalences in `C`,
`CofibrantObject C`, `FibrantObject C` or `BifibrantObject C`.

-/

universe w v u

open CategoryTheory Limits

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C]

namespace BifibrantObject

variable (C) in

def homRel : HomRel (BifibrantObject C) :=
  fun _ _ f g ↦ RightHomotopyRel f.hom g.hom

lemma homRel_iff_leftHomotopyRel {X Y : BifibrantObject C} {f g : X ⟶ Y} :
    homRel C f g ↔ LeftHomotopyRel f.hom g.hom := by
  rw [homRel_iff_rightHomotopyRel, leftHomotopyRel_iff_rightHomotopyRel]

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

variable (C) in

abbrev HoCat := Quotient (BifibrantObject.homRel C)

def toHoCat : BifibrantObject C ⥤ HoCat C := Quotient.functor _

lemma toHoCat_obj_surjective : Function.Surjective (toHoCat (C := C)).obj :=
  fun ⟨_⟩ ↦ ⟨_, rfl⟩

-- INSTANCE (free from Core): :

lemma toHoCat_map_eq {X Y : BifibrantObject C} {f g : X ⟶ Y}
    (h : homRel C f g) :
    toHoCat.map f = toHoCat.map g :=
  CategoryTheory.Quotient.sound _ h

lemma toHoCat_map_eq_iff {X Y : BifibrantObject C} (f g : X ⟶ Y) :
    toHoCat.map f = toHoCat.map g ↔ homRel C f g :=
  Quotient.functor_map_eq_iff _ _ _

-- INSTANCE (free from Core): [LocallySmall.{w}

variable {D : Type*} [Category* D]

def strictUniversalPropertyFixedTargetToHoCat :
    Localization.StrictUniversalPropertyFixedTarget
      toHoCat (weakEquivalences (BifibrantObject C)) D where
  inverts := by
    rw [inverts_iff_factors]
    intro K L f g h
    exact CategoryTheory.Quotient.sound _ h
  lift F hF := CategoryTheory.Quotient.lift _ F
    (by rwa [inverts_iff_factors] at hF)
  fac F hF := rfl
  uniq _ _ h := Quotient.lift_unique' _ _ _ h

end

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): {X

variable {X Y : C} [IsCofibrant X] [IsCofibrant Y] [IsFibrant X] [IsFibrant Y]

def HoCat.homEquivRight :
    RightHomotopyClass X Y ≃ (toHoCat.obj (mk X) ⟶ toHoCat.obj (mk Y)) where
  toFun := Quot.lift (fun f ↦ toHoCat.map (homMk f)) (fun _ _ h ↦ by rwa [toHoCat_map_eq_iff])
  invFun := Quot.lift (fun f ↦ .mk f.hom) (fun _ _ h ↦ by
    simpa [RightHomotopyClass.mk_eq_mk_iff] using h)
  left_inv := by rintro ⟨f⟩; rfl
  right_inv := by rintro ⟨f⟩; rfl
