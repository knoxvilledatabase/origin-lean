/-
Extracted from CategoryTheory/Monoidal/Closed/Functor.lean
Genuine: 11 of 12 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Cartesian closed functors

Define the exponential comparison morphisms for a functor which preserves binary products, and use
them to define a Cartesian closed functor: one which (naturally) preserves exponentials.

Define the Frobenius morphism, and show it is an isomorphism iff the exponential comparison is an
isomorphism.

## TODO
Some of the results here are true more generally for closed objects and for closed monoidal
categories, and these could be generalised.

## References
https://ncatlab.org/nlab/show/cartesian+closed+functor
https://ncatlab.org/nlab/show/Frobenius+reciprocity

## Tags
Frobenius reciprocity, Cartesian closed functor

-/

noncomputable section

namespace CategoryTheory

open Category MonoidalClosed MonoidalCategory CartesianMonoidalCategory TwoSquare

universe v u u'

variable {C : Type u} [Category.{v} C]

variable {D : Type u'} [Category.{v} D]

variable [CartesianMonoidalCategory C] [CartesianMonoidalCategory D]

variable (F : C ⥤ D) {L : D ⥤ C}

def frobeniusMorphism (h : L ⊣ F) (A : C) : TwoSquare (tensorLeft (F.obj A)) L L (tensorLeft A) :=
  prodComparisonNatTrans L (F.obj A) ≫
    Functor.whiskerLeft _ ((curriedTensor C).map (h.counit.app _))

set_option backward.isDefEq.respectTransparency false in

-- INSTANCE (free from Core): frobeniusMorphism_iso_of_preserves_binary_products

variable [MonoidalClosed C] [MonoidalClosed D]

variable [Limits.PreservesLimitsOfShape (Discrete Limits.WalkingPair) F]

def expComparison (A : C) : TwoSquare (ihom A) F F (ihom (F.obj A)) :=
  mateEquiv (ihom.adjunction A) (ihom.adjunction (F.obj A)) (prodComparisonNatIso F A).inv

set_option backward.isDefEq.respectTransparency false in

theorem expComparison_ev (A B : C) :
    F.obj A ◁ ((expComparison F A).natTrans.app B) ≫ (ihom.ev (F.obj A)).app (F.obj B) =
      inv (prodComparison F _ _) ≫ F.map ((ihom.ev _).app _) := by
  convert mateEquiv_counit _ _ (prodComparisonNatIso F A).inv B using 2
  apply IsIso.inv_eq_of_hom_inv_id -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): was `ext`
  simp only [prodComparisonNatTrans_app, prodComparisonNatIso_inv, NatIso.isIso_inv_app,
    IsIso.hom_inv_id]

set_option backward.isDefEq.respectTransparency false in

theorem coev_expComparison (A B : C) :
    F.map ((ihom.coev A).app B) ≫ (expComparison F A).natTrans.app (A ⊗ B) =
      (ihom.coev _).app (F.obj B) ≫ (ihom (F.obj A)).map (inv (prodComparison F A B)) := by
  convert unit_mateEquiv _ _ (prodComparisonNatIso F A).inv B using 3
  apply IsIso.inv_eq_of_hom_inv_id -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): was `ext`
  simp

set_option backward.isDefEq.respectTransparency false in

theorem uncurry_expComparison (A B : C) :
    MonoidalClosed.uncurry ((expComparison F A).natTrans.app B) =
      inv (prodComparison F _ _) ≫ F.map ((ihom.ev _).app _) := by
  rw [uncurry_eq, expComparison_ev]

theorem expComparison_whiskerLeft {A A' : C} (f : A' ⟶ A) :
    (expComparison F A).whiskerBottom (MonoidalClosed.pre (F.map f)) =
      (expComparison F A').whiskerTop (MonoidalClosed.pre f) := by
  unfold expComparison MonoidalClosed.pre
  have vcomp1 := mateEquiv_conjugateEquiv_vcomp
    (ihom.adjunction A) (ihom.adjunction (F.obj A)) (ihom.adjunction (F.obj A'))
    ((prodComparisonNatIso F A).inv) (((curriedTensor D).map (F.map f)))
  have vcomp2 := conjugateEquiv_mateEquiv_vcomp
    (ihom.adjunction A) (ihom.adjunction A') (ihom.adjunction (F.obj A'))
    (((curriedTensor C).map f)) ((prodComparisonNatIso F A').inv)
  rw [← vcomp1, ← vcomp2]
  unfold TwoSquare.whiskerLeft TwoSquare.whiskerRight
  congr 1
  apply congr_arg
  ext B
  simp only [Functor.comp_obj, curriedTensor_obj_obj, prodComparisonNatIso_inv,
    NatTrans.comp_app, Functor.whiskerLeft_app, curriedTensor_map_app, NatIso.isIso_inv_app,
    Functor.whiskerRight_app, IsIso.eq_inv_comp, prodComparisonNatTrans_app]
  rw [← prodComparison_inv_natural_whiskerRight F f]
  simp

class MonoidalClosedFunctor : Prop where
  comparison_iso : ∀ A, IsIso (expComparison F A).natTrans

attribute [instance] MonoidalClosedFunctor.comparison_iso

theorem frobeniusMorphism_mate (h : L ⊣ F) (A : C) :
    conjugateEquiv (h.comp (ihom.adjunction A)) ((ihom.adjunction (F.obj A)).comp h)
        (frobeniusMorphism F h A).natTrans = (expComparison F A).natTrans := by
  unfold expComparison frobeniusMorphism
  have conjeq := iterated_mateEquiv_conjugateEquiv h h
    (ihom.adjunction (F.obj A)) (ihom.adjunction A)
    (prodComparisonNatTrans L (F.obj A) ≫
      Functor.whiskerLeft L ((curriedTensor C).map (h.counit.app A)))
  rw [← conjeq]
  congr 1
  apply congr_arg
  ext B
  unfold mateEquiv
  simp only [Functor.comp_obj, curriedTensor_obj_obj, Equiv.coe_fn_mk, Functor.whiskerRight_comp,
    Functor.whiskerLeft_comp, Category.assoc, NatTrans.comp_app, Functor.id_obj,
    Functor.rightUnitor_inv_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.whiskerRight_app, prodComparisonNatTrans_app,
    curriedTensor_map_app, Functor.comp_map, curriedTensor_obj_map, Functor.leftUnitor_hom_app,
    Category.comp_id, Category.id_comp, prodComparisonNatIso_inv, NatIso.isIso_inv_app]
  rw [← F.map_comp, ← F.map_comp]
  simp only [Functor.map_comp]
  apply IsIso.eq_inv_of_inv_hom_id
  simp only [Category.assoc]
  rw [prodComparison_natural_whiskerLeft, prodComparison_natural_whiskerRight_assoc]
  slice_lhs 2 3 => rw [← prodComparison_comp]
  simp only [Category.assoc]
  unfold prodComparison
  simp

theorem frobeniusMorphism_iso_of_expComparison_iso (h : L ⊣ F) (A : C)
    [i : IsIso (expComparison F A).natTrans] : IsIso (frobeniusMorphism F h A).natTrans := by
  rw [← frobeniusMorphism_mate F h] at i
  exact @conjugateEquiv_of_iso _ _ _ _ _ _ _ _ _ _ _ i

theorem expComparison_iso_of_frobeniusMorphism_iso (h : L ⊣ F) (A : C)
    [i : IsIso (frobeniusMorphism F h A)] : IsIso (expComparison F A).natTrans := by
  rw [← frobeniusMorphism_mate F h]; infer_instance

open Limits in

theorem cartesianClosedFunctorOfLeftAdjointPreservesBinaryProducts (h : L ⊣ F) [F.Full] [F.Faithful]
    [PreservesLimitsOfShape (Discrete WalkingPair) L] : MonoidalClosedFunctor F where
  comparison_iso _ := expComparison_iso_of_frobeniusMorphism_iso F h _

end CategoryTheory
