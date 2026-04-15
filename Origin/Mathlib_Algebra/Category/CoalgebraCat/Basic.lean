/-
Extracted from Algebra/Category/CoalgebraCat/Basic.lean
Genuine: 8 of 27 | Dissolved: 0 | Infrastructure: 19
-/
import Origin.Core
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.RingTheory.Coalgebra.Equiv

/-!
# The category of coalgebras over a commutative ring

We introduce the bundled category `CoalgebraCat` of coalgebras over a fixed commutative ring `R`
along with the forgetful functor to `ModuleCat`.

This file mimics `Mathlib.LinearAlgebra.QuadraticForm.QuadraticModuleCat`.

-/

open CategoryTheory

universe v u

variable (R : Type u) [CommRing R]

structure CoalgebraCat extends ModuleCat.{v} R where
  instCoalgebra : Coalgebra R carrier

attribute [instance] CoalgebraCat.instCoalgebra

variable {R}

namespace CoalgebraCat

open Coalgebra

instance : CoeSort (CoalgebraCat.{v} R) (Type v) :=
  ⟨(·.carrier)⟩

@[simp] theorem moduleCat_of_toModuleCat (X : CoalgebraCat.{v} R) :
    ModuleCat.of R X.toModuleCat = X.toModuleCat :=
  rfl

variable (R)

@[simps]
def of (X : Type v) [AddCommGroup X] [Module R X] [Coalgebra R X] :
    CoalgebraCat R where
  instCoalgebra := (inferInstance : Coalgebra R X)

variable {R}

@[simp]
lemma of_comul {X : Type v} [AddCommGroup X] [Module R X] [Coalgebra R X] :
    Coalgebra.comul (A := of R X) = Coalgebra.comul (R := R) (A := X) := rfl

@[simp]
lemma of_counit {X : Type v} [AddCommGroup X] [Module R X] [Coalgebra R X] :
    Coalgebra.counit (A := of R X) = Coalgebra.counit (R := R) (A := X) := rfl

@[ext]
structure Hom (V W : CoalgebraCat.{v} R) where
  /-- The underlying `CoalgHom` -/
  toCoalgHom : V →ₗc[R] W

lemma Hom.toCoalgHom_injective (V W : CoalgebraCat.{v} R) :
    Function.Injective (Hom.toCoalgHom : Hom V W → _) :=
  fun ⟨f⟩ ⟨g⟩ _ => by congr

instance category : Category (CoalgebraCat.{v} R) where
  Hom M N := Hom M N
  id M := ⟨CoalgHom.id R M⟩
  comp f g := ⟨CoalgHom.comp g.toCoalgHom f.toCoalgHom⟩

@[ext]
lemma hom_ext {M N : CoalgebraCat.{v} R} (f g : M ⟶ N) (h : f.toCoalgHom = g.toCoalgHom) :
    f = g :=
  Hom.ext h

abbrev ofHom {X Y : Type v} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    [Coalgebra R X] [Coalgebra R Y] (f : X →ₗc[R] Y) :
    of R X ⟶ of R Y :=
  ⟨f⟩

@[simp] theorem toCoalgHom_comp {M N U : CoalgebraCat.{v} R} (f : M ⟶ N) (g : N ⟶ U) :
    (f ≫ g).toCoalgHom = g.toCoalgHom.comp f.toCoalgHom :=
  rfl

@[simp] theorem toCoalgHom_id {M : CoalgebraCat.{v} R} :
    Hom.toCoalgHom (𝟙 M) = CoalgHom.id _ _ :=
  rfl

instance concreteCategory : ConcreteCategory.{v} (CoalgebraCat.{v} R) where
  forget :=
    { obj := fun M => M
      map := fun f => f.toCoalgHom }
  forget_faithful :=
    { map_injective := fun {_ _} => DFunLike.coe_injective.comp <| Hom.toCoalgHom_injective _ _ }

instance hasForgetToModule : HasForget₂ (CoalgebraCat R) (ModuleCat R) where
  forget₂ :=
    { obj := fun M => ModuleCat.of R M
      map := fun f => f.toCoalgHom.toLinearMap }

@[simp]
theorem forget₂_obj (X : CoalgebraCat R) :
    (forget₂ (CoalgebraCat R) (ModuleCat R)).obj X = ModuleCat.of R X :=
  rfl

@[simp]
theorem forget₂_map (X Y : CoalgebraCat R) (f : X ⟶ Y) :
    (forget₂ (CoalgebraCat R) (ModuleCat R)).map f = (f.toCoalgHom : X →ₗ[R] Y) :=
  rfl

end CoalgebraCat

namespace CoalgEquiv

open CoalgebraCat

variable {X Y Z : Type v}

variable [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y] [AddCommGroup Z] [Module R Z]

variable [Coalgebra R X] [Coalgebra R Y] [Coalgebra R Z]

@[simps]
def toCoalgebraCatIso (e : X ≃ₗc[R] Y) : CoalgebraCat.of R X ≅ CoalgebraCat.of R Y where
  hom := CoalgebraCat.ofHom e
  inv := CoalgebraCat.ofHom e.symm
  hom_inv_id := Hom.ext <| DFunLike.ext _ _ e.left_inv
  inv_hom_id := Hom.ext <| DFunLike.ext _ _ e.right_inv

@[simp] theorem toCoalgebraCatIso_refl :
    toCoalgebraCatIso (CoalgEquiv.refl R X) = .refl _ :=
  rfl

@[simp] theorem toCoalgebraCatIso_symm (e : X ≃ₗc[R] Y) :
    toCoalgebraCatIso e.symm = (toCoalgebraCatIso e).symm :=
  rfl

@[simp] theorem toCoalgebraCatIso_trans (e : X ≃ₗc[R] Y) (f : Y ≃ₗc[R] Z) :
    toCoalgebraCatIso (e.trans f) = toCoalgebraCatIso e ≪≫ toCoalgebraCatIso f :=
  rfl

end CoalgEquiv

namespace CategoryTheory.Iso

open Coalgebra

variable {X Y Z : CoalgebraCat.{v} R}

def toCoalgEquiv (i : X ≅ Y) : X ≃ₗc[R] Y :=
  { i.hom.toCoalgHom with
    invFun := i.inv.toCoalgHom
    left_inv := fun x => CoalgHom.congr_fun (congr_arg CoalgebraCat.Hom.toCoalgHom i.3) x
    right_inv := fun x => CoalgHom.congr_fun (congr_arg CoalgebraCat.Hom.toCoalgHom i.4) x }

@[simp] theorem toCoalgEquiv_toCoalgHom (i : X ≅ Y) :
    i.toCoalgEquiv = i.hom.toCoalgHom := rfl

@[simp] theorem toCoalgEquiv_refl : toCoalgEquiv (.refl X) = .refl _ _ :=
  rfl

@[simp] theorem toCoalgEquiv_symm (e : X ≅ Y) :
    toCoalgEquiv e.symm = (toCoalgEquiv e).symm :=
  rfl

@[simp] theorem toCoalgEquiv_trans (e : X ≅ Y) (f : Y ≅ Z) :
    toCoalgEquiv (e ≪≫ f) = e.toCoalgEquiv.trans f.toCoalgEquiv :=
  rfl

end CategoryTheory.Iso

instance CoalgebraCat.forget_reflects_isos :
    (forget (CoalgebraCat.{v} R)).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget (CoalgebraCat.{v} R)).map f)
    let e : X ≃ₗc[R] Y := { f.toCoalgHom, i.toEquiv with }
    exact ⟨e.toCoalgebraCatIso.isIso_hom.1⟩
