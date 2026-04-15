/-
Extracted from CategoryTheory/Endomorphism.lean
Genuine: 13 of 28 | Dissolved: 0 | Infrastructure: 15
-/
import Origin.Core
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.CategoryTheory.Groupoid
import Mathlib.CategoryTheory.Opposites

/-!
# Endomorphisms

Definition and basic properties of endomorphisms and automorphisms of an object in a category.

For each `X : C`, we provide `CategoryTheory.End X := X ⟶ X` with a monoid structure,
and `CategoryTheory.Aut X := X ≅ X` with a group structure.
-/

universe v v' u u'

namespace CategoryTheory

def End {C : Type u} [CategoryStruct.{v} C] (X : C) := X ⟶ X

namespace End

section Struct

variable {C : Type u} [CategoryStruct.{v} C] (X : C)

protected instance one : One (End X) := ⟨𝟙 X⟩

protected instance inhabited : Inhabited (End X) := ⟨𝟙 X⟩

protected instance mul : Mul (End X) := ⟨fun x y => y ≫ x⟩

variable {X}

def of (f : X ⟶ X) : End X := f

def asHom (f : End X) : X ⟶ X := f

@[simp, nolint simpNF] -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11215): TODO: use `of`/`asHom`?
theorem one_def : (1 : End X) = 𝟙 X := rfl

@[simp] -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11215): TODO: use `of`/`asHom`?
theorem mul_def (xs ys : End X) : xs * ys = ys ≫ xs := rfl

end Struct

instance monoid {C : Type u} [Category.{v} C] {X : C} : Monoid (End X) where
  mul_one := Category.id_comp
  one_mul := Category.comp_id
  mul_assoc := fun x y z => (Category.assoc z y x).symm

section MulAction

variable {C : Type u} [Category.{v} C]

open Opposite

instance mulActionRight {X Y : C} : MulAction (End Y) (X ⟶ Y) where
  smul r f := f ≫ r
  one_smul := Category.comp_id
  mul_smul _ _ _ := Eq.symm <| Category.assoc _ _ _

instance mulActionLeft {X : Cᵒᵖ} {Y : C} : MulAction (End X) (unop X ⟶ Y) where
  smul r f := r.unop ≫ f
  one_smul := Category.id_comp
  mul_smul _ _ _ := Category.assoc _ _ _

theorem smul_right {X Y : C} {r : End Y} {f : X ⟶ Y} : r • f = f ≫ r :=
  rfl

theorem smul_left {X : Cᵒᵖ} {Y : C} {r : End X} {f : unop X ⟶ Y} : r • f = r.unop ≫ f :=
  rfl

end MulAction

instance group {C : Type u} [Groupoid.{v} C] (X : C) : Group (End X) where
  inv_mul_cancel := Groupoid.comp_inv
  inv := Groupoid.inv

end End

theorem isUnit_iff_isIso {C : Type u} [Category.{v} C] {X : C} (f : End X) :
    IsUnit (f : End X) ↔ IsIso f :=
  ⟨fun h => { out := ⟨h.unit.inv, ⟨h.unit.inv_val, h.unit.val_inv⟩⟩ }, fun h =>
    ⟨⟨f, inv f, by simp, by simp⟩, rfl⟩⟩

variable {C : Type u} [Category.{v} C] (X : C)

def Aut (X : C) := X ≅ X

namespace Aut

@[ext]
lemma ext {X : C} {φ₁ φ₂ : Aut X} (h : φ₁.hom = φ₂.hom) : φ₁ = φ₂ :=
  Iso.ext h

protected instance inhabited : Inhabited (Aut X) := ⟨Iso.refl X⟩

instance : Group (Aut X) where
  one := Iso.refl X
  inv := Iso.symm
  mul x y := Iso.trans y x
  mul_assoc _ _ _ := (Iso.trans_assoc _ _ _).symm
  one_mul := Iso.trans_refl
  mul_one := Iso.refl_trans
  inv_mul_cancel := Iso.self_symm_id

theorem Aut_mul_def (f g : Aut X) : f * g = g.trans f := rfl

theorem Aut_inv_def (f : Aut X) : f⁻¹ = f.symm := rfl

def unitsEndEquivAut : (End X)ˣ ≃* Aut X where
  toFun f := ⟨f.1, f.2, f.4, f.3⟩
  invFun f := ⟨f.1, f.2, f.4, f.3⟩
  left_inv := fun ⟨_, _, _, _⟩ => rfl
  right_inv := fun ⟨_, _, _, _⟩ => rfl
  map_mul' f g := by cases f; cases g; rfl

@[simps!]
def toEnd (X : C) : Aut X →* End X := (Units.coeHom (End X)).comp (Aut.unitsEndEquivAut X).symm

def autMulEquivOfIso {X Y : C} (h : X ≅ Y) : Aut X ≃* Aut Y where
  toFun x := { hom := h.inv ≫ x.hom ≫ h.hom, inv := h.inv ≫ x.inv ≫ h.hom }
  invFun y := { hom := h.hom ≫ y.hom ≫ h.inv, inv := h.hom ≫ y.inv ≫ h.inv }
  left_inv _ := by aesop_cat
  right_inv _ := by aesop_cat
  map_mul' := by simp [Aut_mul_def]

end Aut

namespace Functor

variable {D : Type u'} [Category.{v'} D] (f : C ⥤ D)

@[simps]
def mapEnd : End X →* End (f.obj X) where
  toFun := f.map
  map_mul' x y := f.map_comp y x
  map_one' := f.map_id X

def mapAut : Aut X →* Aut (f.obj X) where
  toFun := f.mapIso
  map_mul' x y := f.mapIso_trans y x
  map_one' := f.mapIso_refl X

namespace FullyFaithful

variable {f}

variable (hf : FullyFaithful f)

@[simps!]
noncomputable def mulEquivEnd (X : C) :
    End X ≃* End (f.obj X) where
  toEquiv := hf.homEquiv
  __ := mapEnd X f

@[simps!]
noncomputable def autMulEquivOfFullyFaithful (X : C) :
    Aut X ≃* Aut (f.obj X) where
  toEquiv := hf.isoEquiv
  __ := mapAut X f

end FullyFaithful

end Functor

end CategoryTheory
