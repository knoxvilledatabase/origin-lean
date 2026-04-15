/-
Extracted from CategoryTheory/Monoidal/Internal/FunctorCategory.lean
Genuine: 19 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.CategoryTheory.Monoidal.CommMon_
import Mathlib.CategoryTheory.Monoidal.Comon_
import Mathlib.CategoryTheory.Monoidal.FunctorCategory

/-!
# `Mon_ (C ⥤ D) ≌ C ⥤ Mon_ D`

When `D` is a monoidal category,
monoid objects in `C ⥤ D` are the same thing as functors from `C` into the monoid objects of `D`.

This is formalised as:
* `monFunctorCategoryEquivalence : Mon_ (C ⥤ D) ≌ C ⥤ Mon_ D`

The intended application is that as `Ring ≌ Mon_ Ab` (not yet constructed!),
we have `presheaf Ring X ≌ presheaf (Mon_ Ab) X ≌ Mon_ (presheaf Ab X)`,
and we can model a module over a presheaf of rings as a module object in `presheaf Ab X`.

## Future work
Presumably this statement is not specific to monoids,
and could be generalised to any internal algebraic objects,
if the appropriate framework was available.
-/

universe v₁ v₂ u₁ u₂

open CategoryTheory MonoidalCategory

namespace CategoryTheory.Monoidal

variable (C : Type u₁) [Category.{v₁} C]

variable (D : Type u₂) [Category.{v₂} D] [MonoidalCategory.{v₂} D]

namespace MonFunctorCategoryEquivalence

variable {C D}

@[simps]
def functorObj (A : Mon_ (C ⥤ D)) : C ⥤ Mon_ D where
  obj X :=
  { X := A.X.obj X
    one := A.one.app X
    mul := A.mul.app X
    one_mul := congr_app A.one_mul X
    mul_one := congr_app A.mul_one X
    mul_assoc := congr_app A.mul_assoc X }
  map f :=
  { hom := A.X.map f
    one_hom := by rw [← A.one.naturality, tensorUnit_map]; dsimp; rw [Category.id_comp]
    mul_hom := by dsimp; rw [← A.mul.naturality, tensorObj_map] }
  map_id X := by ext; dsimp; rw [CategoryTheory.Functor.map_id]
  map_comp f g := by ext; dsimp; rw [Functor.map_comp]

@[simps]
def functor : Mon_ (C ⥤ D) ⥤ C ⥤ Mon_ D where
  obj := functorObj
  map f :=
  { app := fun X =>
    { hom := f.hom.app X
      one_hom := congr_app f.one_hom X
      mul_hom := congr_app f.mul_hom X } }

@[simps]
def inverseObj (F : C ⥤ Mon_ D) : Mon_ (C ⥤ D) where
  X := F ⋙ Mon_.forget D
  one := { app := fun X => (F.obj X).one }
  mul := { app := fun X => (F.obj X).mul }

@[simps]
def inverse : (C ⥤ Mon_ D) ⥤ Mon_ (C ⥤ D) where
  obj := inverseObj
  map α :=
  { hom :=
    { app := fun X => (α.app X).hom
      naturality := fun _ _ f => congr_arg Mon_.Hom.hom (α.naturality f) } }

@[simps!]
def unitIso : 𝟭 (Mon_ (C ⥤ D)) ≅ functor ⋙ inverse :=
  NatIso.ofComponents (fun A =>
  { hom := { hom := { app := fun _ => 𝟙 _ } }
    inv := { hom := { app := fun _ => 𝟙 _ } } })

@[simps!]
def counitIso : inverse ⋙ functor ≅ 𝟭 (C ⥤ Mon_ D) :=
  NatIso.ofComponents (fun A =>
    NatIso.ofComponents (fun X => { hom := { hom := 𝟙 _ }, inv := { hom := 𝟙 _ } }))

end MonFunctorCategoryEquivalence

open MonFunctorCategoryEquivalence

@[simps]
def monFunctorCategoryEquivalence : Mon_ (C ⥤ D) ≌ C ⥤ Mon_ D where
  functor := functor
  inverse := inverse
  unitIso := unitIso
  counitIso := counitIso

namespace ComonFunctorCategoryEquivalence

variable {C D}

@[simps]
def functorObj (A : Comon_ (C ⥤ D)) : C ⥤ Comon_ D where
  obj X :=
  { X := A.X.obj X
    counit := A.counit.app X
    comul := A.comul.app X
    counit_comul := congr_app A.counit_comul X
    comul_counit := congr_app A.comul_counit X
    comul_assoc := congr_app A.comul_assoc X }
  map f :=
  { hom := A.X.map f
    hom_counit := by dsimp; rw [A.counit.naturality, tensorUnit_map]; dsimp; rw [Category.comp_id]
    hom_comul := by dsimp; rw [A.comul.naturality, tensorObj_map] }
  map_id X := by ext; dsimp; rw [CategoryTheory.Functor.map_id]
  map_comp f g := by ext; dsimp; rw [Functor.map_comp]

@[simps]
def functor : Comon_ (C ⥤ D) ⥤ C ⥤ Comon_ D where
  obj := functorObj
  map f :=
  { app := fun X =>
    { hom := f.hom.app X
      hom_counit := congr_app f.hom_counit X
      hom_comul := congr_app f.hom_comul X } }

@[simps]
def inverseObj (F : C ⥤ Comon_ D) : Comon_ (C ⥤ D) where
  X := F ⋙ Comon_.forget D
  counit := { app := fun X => (F.obj X).counit }
  comul := { app := fun X => (F.obj X).comul }

@[simps]
private def inverse : (C ⥤ Comon_ D) ⥤ Comon_ (C ⥤ D) where
  obj := inverseObj
  map α :=
  { hom :=
    { app := fun X => (α.app X).hom
      naturality := fun _ _ f => congr_arg Comon_.Hom.hom (α.naturality f) }
    hom_counit := by ext x; dsimp; rw [(α.app x).hom_counit]
    hom_comul := by ext x; dsimp; rw [(α.app x).hom_comul] }

@[simps!]
private def unitIso : 𝟭 (Comon_ (C ⥤ D)) ≅ functor ⋙ inverse :=
  NatIso.ofComponents (fun A =>
  { hom := { hom := { app := fun _ => 𝟙 _ } }
    inv := { hom := { app := fun _ => 𝟙 _ } } })

@[simps!]
def counitIso : inverse ⋙ functor ≅ 𝟭 (C ⥤ Comon_ D) :=
  NatIso.ofComponents (fun A =>
    NatIso.ofComponents (fun X => { hom := { hom := 𝟙 _ }, inv := { hom := 𝟙 _ } }) )

end ComonFunctorCategoryEquivalence

open ComonFunctorCategoryEquivalence

@[simps]
def comonFunctorCategoryEquivalence : Comon_ (C ⥤ D) ≌ C ⥤ Comon_ D where
  functor := functor
  inverse := inverse
  unitIso := unitIso
  counitIso := counitIso

variable [BraidedCategory.{v₂} D]

namespace CommMonFunctorCategoryEquivalence

variable {C D}

@[simps!]
def functor : CommMon_ (C ⥤ D) ⥤ C ⥤ CommMon_ D where
  obj A :=
    { (monFunctorCategoryEquivalence C D).functor.obj A.toMon_ with
      obj := fun X =>
        { ((monFunctorCategoryEquivalence C D).functor.obj A.toMon_).obj X with
          mul_comm := congr_app A.mul_comm X } }
  map f := { app := fun X => ((monFunctorCategoryEquivalence C D).functor.map f).app X }

@[simps!]
def inverse : (C ⥤ CommMon_ D) ⥤ CommMon_ (C ⥤ D) where
  obj F :=
    { (monFunctorCategoryEquivalence C D).inverse.obj (F ⋙ CommMon_.forget₂Mon_ D) with
      mul_comm := by ext X; exact (F.obj X).mul_comm }
  map α := (monFunctorCategoryEquivalence C D).inverse.map (whiskerRight α _)

@[simps!]
def unitIso : 𝟭 (CommMon_ (C ⥤ D)) ≅ functor ⋙ inverse :=
  NatIso.ofComponents (fun A =>
  { hom := { hom := { app := fun _ => 𝟙 _ }  }
    inv := { hom := { app := fun _ => 𝟙 _ }  } })

@[simps!]
def counitIso : inverse ⋙ functor ≅ 𝟭 (C ⥤ CommMon_ D) :=
  NatIso.ofComponents (fun A =>
    NatIso.ofComponents (fun X => { hom := { hom := 𝟙 _ }, inv := { hom := 𝟙 _ } }) )

end CommMonFunctorCategoryEquivalence

open CommMonFunctorCategoryEquivalence

@[simps]
def commMonFunctorCategoryEquivalence : CommMon_ (C ⥤ D) ≌ C ⥤ CommMon_ D where
  functor := functor
  inverse := inverse
  unitIso := unitIso
  counitIso := counitIso

end CategoryTheory.Monoidal
