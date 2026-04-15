/-
Extracted from CategoryTheory/Category/Bipointed.lean
Genuine: 16 of 29 | Dissolved: 0 | Infrastructure: 13
-/
import Origin.Core
import Mathlib.CategoryTheory.Category.Pointed

/-!
# The category of bipointed types

This defines `Bipointed`, the category of bipointed types.

## TODO

Monoidal structure
-/

open CategoryTheory

universe u

structure Bipointed : Type (u + 1) where
  /-- The underlying type of a bipointed type. -/
  protected X : Type u
  /-- The two points of a bipointed type, bundled together as a pair. -/
  toProd : X × X

namespace Bipointed

instance : CoeSort Bipointed Type* := ⟨Bipointed.X⟩

def of {X : Type*} (to_prod : X × X) : Bipointed :=
  ⟨X, to_prod⟩

@[simp]
theorem coe_of {X : Type*} (to_prod : X × X) : ↥(of to_prod) = X :=
  rfl

alias _root_.Prod.Bipointed := of

instance : Inhabited Bipointed :=
  ⟨of ((), ())⟩

@[ext]
protected structure Hom (X Y : Bipointed.{u}) : Type u where
  /-- The underlying function of a morphism of bipointed types. -/
  toFun : X → Y
  map_fst : toFun X.toProd.1 = Y.toProd.1
  map_snd : toFun X.toProd.2 = Y.toProd.2

namespace Hom

@[simps]
nonrec def id (X : Bipointed) : Bipointed.Hom X X :=
  ⟨id, rfl, rfl⟩

instance (X : Bipointed) : Inhabited (Bipointed.Hom X X) :=
  ⟨id X⟩

@[simps]
def comp {X Y Z : Bipointed.{u}} (f : Bipointed.Hom X Y) (g : Bipointed.Hom Y Z) :
    Bipointed.Hom X Z :=
  ⟨g.toFun ∘ f.toFun, by rw [Function.comp_apply, f.map_fst, g.map_fst], by
    rw [Function.comp_apply, f.map_snd, g.map_snd]⟩

end Hom

instance largeCategory : LargeCategory Bipointed where
  Hom := Bipointed.Hom
  id := Hom.id
  comp := @Hom.comp

instance concreteCategory : ConcreteCategory Bipointed where
  forget :=
    { obj := Bipointed.X
      map := @Hom.toFun }
  forget_faithful := ⟨@Hom.ext⟩

@[simps]
def swap : Bipointed ⥤ Bipointed where
  obj X := ⟨X, X.toProd.swap⟩
  map f := ⟨f.toFun, f.map_snd, f.map_fst⟩

@[simps!]
def swapEquiv : Bipointed ≌ Bipointed where
  functor := swap
  inverse := swap
  unitIso := Iso.refl _
  counitIso := Iso.refl _

@[simp]
theorem swapEquiv_symm : swapEquiv.symm = swapEquiv :=
  rfl

end Bipointed

def bipointedToPointedFst : Bipointed ⥤ Pointed where
  obj X := ⟨X, X.toProd.1⟩
  map f := ⟨f.toFun, f.map_fst⟩

def bipointedToPointedSnd : Bipointed ⥤ Pointed where
  obj X := ⟨X, X.toProd.2⟩
  map f := ⟨f.toFun, f.map_snd⟩

@[simp]
theorem bipointedToPointedFst_comp_forget :
    bipointedToPointedFst ⋙ forget Pointed = forget Bipointed :=
  rfl

@[simp]
theorem bipointedToPointedSnd_comp_forget :
    bipointedToPointedSnd ⋙ forget Pointed = forget Bipointed :=
  rfl

@[simp]
theorem swap_comp_bipointedToPointedFst :
    Bipointed.swap ⋙ bipointedToPointedFst = bipointedToPointedSnd :=
  rfl

@[simp]
theorem swap_comp_bipointedToPointedSnd :
    Bipointed.swap ⋙ bipointedToPointedSnd = bipointedToPointedFst :=
  rfl

def pointedToBipointed : Pointed.{u} ⥤ Bipointed where
  obj X := ⟨X, X.point, X.point⟩
  map f := ⟨f.toFun, f.map_point, f.map_point⟩

def pointedToBipointedFst : Pointed.{u} ⥤ Bipointed where
  obj X := ⟨Option X, X.point, none⟩
  map f := ⟨Option.map f.toFun, congr_arg _ f.map_point, rfl⟩
  map_id _ := Bipointed.Hom.ext Option.map_id
  map_comp f g := Bipointed.Hom.ext (Option.map_comp_map f.1 g.1).symm

def pointedToBipointedSnd : Pointed.{u} ⥤ Bipointed where
  obj X := ⟨Option X, none, X.point⟩
  map f := ⟨Option.map f.toFun, rfl, congr_arg _ f.map_point⟩
  map_id _ := Bipointed.Hom.ext Option.map_id
  map_comp f g := Bipointed.Hom.ext (Option.map_comp_map f.1 g.1).symm

@[simp]
theorem pointedToBipointedFst_comp_swap :
    pointedToBipointedFst ⋙ Bipointed.swap = pointedToBipointedSnd :=
  rfl

@[simp]
theorem pointedToBipointedSnd_comp_swap :
    pointedToBipointedSnd ⋙ Bipointed.swap = pointedToBipointedFst :=
  rfl

@[simps!]
def pointedToBipointedCompBipointedToPointedFst :
    pointedToBipointed ⋙ bipointedToPointedFst ≅ 𝟭 _ :=
  NatIso.ofComponents fun X =>
    { hom := ⟨id, rfl⟩
      inv := ⟨id, rfl⟩ }

@[simps!]
def pointedToBipointedCompBipointedToPointedSnd :
    pointedToBipointed ⋙ bipointedToPointedSnd ≅ 𝟭 _ :=
  NatIso.ofComponents fun X =>
    { hom := ⟨id, rfl⟩
      inv := ⟨id, rfl⟩ }

def pointedToBipointedFstBipointedToPointedFstAdjunction :
    pointedToBipointedFst ⊣ bipointedToPointedFst :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f => ⟨f.toFun ∘ Option.some, f.map_fst⟩
          invFun := fun f => ⟨fun o => o.elim Y.toProd.2 f.toFun, f.map_point, rfl⟩
          left_inv := fun f => by
            apply Bipointed.Hom.ext
            funext x
            cases x
            · exact f.map_snd.symm
            · rfl
          right_inv := fun _ => Pointed.Hom.ext rfl }
      homEquiv_naturality_left_symm := fun f g => by
        apply Bipointed.Hom.ext
        funext x
        cases x <;> rfl }

def pointedToBipointedSndBipointedToPointedSndAdjunction :
    pointedToBipointedSnd ⊣ bipointedToPointedSnd :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f => ⟨f.toFun ∘ Option.some, f.map_snd⟩
          invFun := fun f => ⟨fun o => o.elim Y.toProd.1 f.toFun, rfl, f.map_point⟩
          left_inv := fun f => by
            apply Bipointed.Hom.ext
            funext x
            cases x
            · exact f.map_fst.symm
            · rfl
          right_inv := fun _ => Pointed.Hom.ext rfl }
      homEquiv_naturality_left_symm := fun f g => by
        apply Bipointed.Hom.ext
        funext x
        cases x <;> rfl }
