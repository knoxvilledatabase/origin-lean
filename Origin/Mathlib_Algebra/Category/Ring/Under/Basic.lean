/-
Extracted from Algebra/Category/Ring/Under/Basic.lean
Genuine: 10 | Conflates: 0 | Dissolved: 0 | Infrastructure: 11
-/
import Origin.Core
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.CategoryTheory.Adjunction.Over

noncomputable section

/-!
# Under `CommRingCat`

In this file we provide basic API for `Under R` when `R : CommRingCat`. `Under R` is
(equivalent to) the category of commutative `R`-algebras. For not necessarily commutative
algebras, use `AlgebraCat R` instead.
-/

noncomputable section

universe u

open TensorProduct CategoryTheory Limits

variable {R S : CommRingCat.{u}}

namespace CommRingCat

instance : CoeSort (Under R) (Type u) where
  coe A := A.right

instance (A : Under R) : Algebra R A := RingHom.toAlgebra A.hom

def toAlgHom {A B : Under R} (f : A ⟶ B) : A →ₐ[R] B where
  __ := f.right
  commutes' a := by
    have : (A.hom ≫ f.right) a = B.hom a := by simp
    simpa only [Functor.const_obj_obj, Functor.id_obj, CommRingCat.comp_apply] using this

variable (R) in

@[simps! hom, simps! (config := .lemmasOnly) right]
def mkUnder (A : Type u) [CommRing A] [Algebra R A] : Under R :=
  Under.mk (CommRingCat.ofHom <| algebraMap R A)

@[ext]
lemma mkUnder_ext {A : Type u} [CommRing A] [Algebra R A] {B : Under R}
    {f g : mkUnder R A ⟶ B} (h : ∀ a : A, f.right a = g.right a) :
    f = g := by
  ext x
  exact h x

end CommRingCat

namespace AlgHom

def toUnder {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (f : A →ₐ[R] B) : CommRingCat.mkUnder R A ⟶ CommRingCat.mkUnder R B :=
  Under.homMk f.toRingHom <| by
    ext a
    exact f.commutes' a

end AlgHom

namespace AlgEquiv

def toUnder {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (f : A ≃ₐ[R] B) :
    CommRingCat.mkUnder R A ≅ CommRingCat.mkUnder R B where
  hom := f.toAlgHom.toUnder
  inv := f.symm.toAlgHom.toUnder
  hom_inv_id := by
    ext (a : (CommRingCat.mkUnder R A).right)
    simp
  inv_hom_id := by
    ext a
    simp

end AlgEquiv

namespace CommRingCat

variable [Algebra R S]

variable (R S) in

@[simps! map_right]
def tensorProd : Under R ⥤ Under S where
  obj A := mkUnder S (S ⊗[R] A)
  map f := Algebra.TensorProduct.map (AlgHom.id S S) (toAlgHom f) |>.toUnder
  map_comp {X Y Z} f g := by simp [Algebra.TensorProduct.map_id_comp]

variable (S) in

def tensorProdObjIsoPushoutObj (A : Under R) :
    mkUnder S (S ⊗[R] A) ≅ (Under.pushout (algebraMap R S)).obj A :=
  Under.isoMk (CommRingCat.isPushout_tensorProduct R S A).flip.isoPushout <| by
    simp only [Functor.const_obj_obj, Under.pushout_obj, Functor.id_obj, Under.mk_right,
      mkUnder_hom, AlgHom.toRingHom_eq_coe, IsPushout.inr_isoPushout_hom, Under.mk_hom]
    rfl

@[reassoc (attr := simp)]
lemma pushout_inl_tensorProdObjIsoPushoutObj_inv_right (A : Under R) :
    pushout.inl A.hom (algebraMap R S) ≫ (tensorProdObjIsoPushoutObj S A).inv.right =
      (CommRingCat.ofHom <| Algebra.TensorProduct.includeRight.toRingHom) := by
  simp [tensorProdObjIsoPushoutObj]

@[reassoc (attr := simp)]
lemma pushout_inr_tensorProdObjIsoPushoutObj_inv_right (A : Under R) :
    pushout.inr A.hom (algebraMap R S) ≫
      (tensorProdObjIsoPushoutObj S A).inv.right =
      (CommRingCat.ofHom <| Algebra.TensorProduct.includeLeftRingHom) := by
  simp [tensorProdObjIsoPushoutObj]

variable (R S) in

def tensorProdIsoPushout : tensorProd R S ≅ Under.pushout (algebraMap R S) :=
  NatIso.ofComponents (fun A ↦ tensorProdObjIsoPushoutObj S A) <| by
    intro A B f
    dsimp
    rw [← cancel_epi (tensorProdObjIsoPushoutObj S A).inv]
    ext : 1
    apply pushout.hom_ext
    · rw [← cancel_mono (tensorProdObjIsoPushoutObj S B).inv.right]
      ext x
      simp [mkUnder_right]
    · rw [← cancel_mono (tensorProdObjIsoPushoutObj S B).inv.right]
      ext (x : S)
      simp [mkUnder_right]

end CommRingCat
