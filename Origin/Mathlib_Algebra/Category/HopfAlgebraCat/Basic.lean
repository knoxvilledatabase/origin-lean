/-
Extracted from Algebra/Category/HopfAlgebraCat/Basic.lean
Genuine: 8 | Conflates: 0 | Dissolved: 0 | Infrastructure: 18
-/
import Origin.Core
import Mathlib.Algebra.Category.BialgebraCat.Basic
import Mathlib.RingTheory.HopfAlgebra

noncomputable section

/-!
# The category of Hopf algebras over a commutative ring

We introduce the bundled category `HopfAlgebraCat` of Hopf algebras over a fixed commutative ring
`R` along with the forgetful functor to `BialgebraCat`.

This file mimics `Mathlib.LinearAlgebra.QuadraticForm.QuadraticModuleCat`.

-/

open CategoryTheory

universe v u

variable (R : Type u) [CommRing R]

structure HopfAlgebraCat extends Bundled Ring.{v} where
  [instHopfAlgebra : HopfAlgebra R α]

attribute [instance] HopfAlgebraCat.instHopfAlgebra

variable {R}

namespace HopfAlgebraCat

open HopfAlgebra

instance : CoeSort (HopfAlgebraCat.{v} R) (Type v) :=
  ⟨(·.α)⟩

variable (R)

@[simps]
def of (X : Type v) [Ring X] [HopfAlgebra R X] :
    HopfAlgebraCat R where
  α := X
  instHopfAlgebra := (inferInstance : HopfAlgebra R X)

variable {R}

@[ext]
structure Hom (V W : HopfAlgebraCat.{v} R) where
  /-- The underlying `BialgHom`. -/
  toBialgHom : V →ₐc[R] W

lemma Hom.toBialgHom_injective (V W : HopfAlgebraCat.{v} R) :
    Function.Injective (Hom.toBialgHom : Hom V W → _) :=
  fun ⟨f⟩ ⟨g⟩ _ => by congr

instance category : Category (HopfAlgebraCat.{v} R) where
  Hom X Y := Hom X Y
  id X := ⟨BialgHom.id R X⟩
  comp f g := ⟨BialgHom.comp g.toBialgHom f.toBialgHom⟩

@[ext]
lemma hom_ext {X Y : HopfAlgebraCat.{v} R} (f g : X ⟶ Y) (h : f.toBialgHom = g.toBialgHom) :
    f = g :=
  Hom.ext h

abbrev ofHom {X Y : Type v} [Ring X] [Ring Y]
    [HopfAlgebra R X] [HopfAlgebra R Y] (f : X →ₐc[R] Y) :
    of R X ⟶ of R Y :=
  ⟨f⟩

instance concreteCategory : ConcreteCategory.{v} (HopfAlgebraCat.{v} R) where
  forget :=
    { obj := fun M => M
      map := fun f => f.toBialgHom }
  forget_faithful :=
    { map_injective := fun {_ _} => DFunLike.coe_injective.comp <| Hom.toBialgHom_injective _ _ }

instance hasForgetToBialgebra : HasForget₂ (HopfAlgebraCat R) (BialgebraCat R) where
  forget₂ :=
    { obj := fun X => BialgebraCat.of R X
      map := fun {_ _} f => BialgebraCat.ofHom f.toBialgHom }

end HopfAlgebraCat

namespace BialgEquiv

open HopfAlgebraCat

variable {X Y Z : Type v}

variable [Ring X] [Ring Y] [Ring Z]

variable [HopfAlgebra R X] [HopfAlgebra R Y] [HopfAlgebra R Z]

@[simps]
def toHopfAlgebraCatIso (e : X ≃ₐc[R] Y) : HopfAlgebraCat.of R X ≅ HopfAlgebraCat.of R Y where
  hom := HopfAlgebraCat.ofHom e
  inv := HopfAlgebraCat.ofHom e.symm
  hom_inv_id := Hom.ext <| DFunLike.ext _ _ e.left_inv
  inv_hom_id := Hom.ext <| DFunLike.ext _ _ e.right_inv

end BialgEquiv

namespace CategoryTheory.Iso

open HopfAlgebra

variable {X Y Z : HopfAlgebraCat.{v} R}

def toHopfAlgEquiv (i : X ≅ Y) : X ≃ₐc[R] Y :=
  { i.hom.toBialgHom with
    invFun := i.inv.toBialgHom
    left_inv := fun x => BialgHom.congr_fun (congr_arg HopfAlgebraCat.Hom.toBialgHom i.3) x
    right_inv := fun x => BialgHom.congr_fun (congr_arg HopfAlgebraCat.Hom.toBialgHom i.4) x }

end CategoryTheory.Iso

instance HopfAlgebraCat.forget_reflects_isos :
    (forget (HopfAlgebraCat.{v} R)).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget (HopfAlgebraCat.{v} R)).map f)
    let e : X ≃ₐc[R] Y := { f.toBialgHom, i.toEquiv with }
    exact ⟨e.toHopfAlgebraCatIso.isIso_hom.1⟩
