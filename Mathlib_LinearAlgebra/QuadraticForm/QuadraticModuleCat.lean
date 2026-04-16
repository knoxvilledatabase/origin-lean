/-
Extracted from LinearAlgebra/QuadraticForm/QuadraticModuleCat.lean
Genuine: 8 | Conflates: 0 | Dissolved: 0 | Infrastructure: 15
-/
import Origin.Core
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
import Mathlib.Algebra.Category.ModuleCat.Basic

noncomputable section

/-!
# The category of quadratic modules
-/

open CategoryTheory

universe v u

variable (R : Type u) [CommRing R]

structure QuadraticModuleCat extends ModuleCat.{v} R where
  /-- The quadratic form associated with the module. -/
  form : QuadraticForm R carrier

variable {R}

namespace QuadraticModuleCat

open QuadraticForm QuadraticMap

instance : CoeSort (QuadraticModuleCat.{v} R) (Type v) :=
  ⟨(·.carrier)⟩

@[simp] theorem moduleCat_of_toModuleCat (X : QuadraticModuleCat.{v} R) :
    ModuleCat.of R X.toModuleCat = X.toModuleCat :=
  rfl

@[simps form]
def of {X : Type v} [AddCommGroup X] [Module R X] (Q : QuadraticForm R X) :
    QuadraticModuleCat R where
  form := Q

@[ext]
structure Hom (V W : QuadraticModuleCat.{v} R) where
  /-- The underlying isometry -/
  toIsometry : V.form →qᵢ W.form

lemma Hom.toIsometry_injective (V W : QuadraticModuleCat.{v} R) :
    Function.Injective (Hom.toIsometry : Hom V W → _) :=
  fun ⟨f⟩ ⟨g⟩ _ => by congr

instance category : Category (QuadraticModuleCat.{v} R) where
  Hom M N := Hom M N
  id M := ⟨Isometry.id M.form⟩
  comp f g := ⟨Isometry.comp g.toIsometry f.toIsometry⟩
  id_comp g := Hom.ext <| Isometry.id_comp g.toIsometry
  comp_id f := Hom.ext <| Isometry.comp_id f.toIsometry
  assoc f g h := Hom.ext <| Isometry.comp_assoc h.toIsometry g.toIsometry f.toIsometry

@[ext]
lemma hom_ext {M N : QuadraticModuleCat.{v} R} (f g : M ⟶ N) (h : f.toIsometry = g.toIsometry) :
    f = g :=
  Hom.ext h

abbrev ofHom {X : Type v} [AddCommGroup X] [Module R X]
    {Q₁ : QuadraticForm R X} {Q₂ : QuadraticForm R X} (f : Q₁ →qᵢ Q₂) :
    of Q₁ ⟶ of Q₂ :=
  ⟨f⟩

@[simp] theorem toIsometry_comp {M N U : QuadraticModuleCat.{v} R} (f : M ⟶ N) (g : N ⟶ U) :
    (f ≫ g).toIsometry = g.toIsometry.comp f.toIsometry :=
  rfl

@[simp] theorem toIsometry_id {M : QuadraticModuleCat.{v} R} :
    Hom.toIsometry (𝟙 M) = Isometry.id _ :=
  rfl

instance concreteCategory : ConcreteCategory.{v} (QuadraticModuleCat.{v} R) where
  forget :=
    { obj := fun M => M
      map := fun f => f.toIsometry }
  forget_faithful :=
    { map_injective := fun {_ _} => DFunLike.coe_injective.comp <| Hom.toIsometry_injective _ _ }

instance hasForgetToModule : HasForget₂ (QuadraticModuleCat R) (ModuleCat R) where
  forget₂ :=
    { obj := fun M => ModuleCat.of R M
      map := fun f => f.toIsometry.toLinearMap }

@[simp]
theorem forget₂_obj (X : QuadraticModuleCat R) :
    (forget₂ (QuadraticModuleCat R) (ModuleCat R)).obj X = ModuleCat.of R X :=
  rfl

@[simp]
theorem forget₂_map (X Y : QuadraticModuleCat R) (f : X ⟶ Y) :
    (forget₂ (QuadraticModuleCat R) (ModuleCat R)).map f = f.toIsometry.toLinearMap :=
  rfl

variable {X Y Z : Type v}

variable [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y] [AddCommGroup Z] [Module R Z]

variable {Q₁ : QuadraticForm R X} {Q₂ : QuadraticForm R Y} {Q₃ : QuadraticForm R Z}

@[simps]
def ofIso (e : Q₁.IsometryEquiv Q₂) : QuadraticModuleCat.of Q₁ ≅ QuadraticModuleCat.of Q₂ where
  hom := ⟨e.toIsometry⟩
  inv := ⟨e.symm.toIsometry⟩
  hom_inv_id := Hom.ext <| DFunLike.ext _ _ e.left_inv
  inv_hom_id := Hom.ext <| DFunLike.ext _ _ e.right_inv

@[simp] theorem ofIso_refl : ofIso (IsometryEquiv.refl Q₁) = .refl _ :=
  rfl

@[simp] theorem ofIso_symm (e : Q₁.IsometryEquiv Q₂) : ofIso e.symm = (ofIso e).symm :=
  rfl

@[simp] theorem ofIso_trans (e : Q₁.IsometryEquiv Q₂) (f : Q₂.IsometryEquiv Q₃) :
    ofIso (e.trans f) = ofIso e ≪≫ ofIso f :=
  rfl

end QuadraticModuleCat

namespace CategoryTheory.Iso

open QuadraticForm

variable {X Y Z : QuadraticModuleCat.{v} R}

@[simps]
def toIsometryEquiv (i : X ≅ Y) : X.form.IsometryEquiv Y.form where
  toFun := i.hom.toIsometry
  invFun := i.inv.toIsometry
  left_inv x := by
    change (i.hom ≫ i.inv).toIsometry x = x
    simp
  right_inv x := by
    change (i.inv ≫ i.hom).toIsometry x = x
    simp
  map_add' := map_add _
  map_smul' := map_smul _
  map_app' := QuadraticMap.Isometry.map_app _

@[simp] theorem toIsometryEquiv_refl : toIsometryEquiv (.refl X) = .refl _ :=
  rfl

@[simp] theorem toIsometryEquiv_symm (e : X ≅ Y) :
    toIsometryEquiv e.symm = (toIsometryEquiv e).symm :=
  rfl

@[simp] theorem toIsometryEquiv_trans (e : X ≅ Y) (f : Y ≅ Z) :
    toIsometryEquiv (e ≪≫ f) = e.toIsometryEquiv.trans f.toIsometryEquiv :=
  rfl

end CategoryTheory.Iso
