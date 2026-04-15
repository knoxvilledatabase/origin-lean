/-
Extracted from CategoryTheory/Abelian/Injective/Ext.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Computing `Ext` using an injective resolution

Given an injective resolution `R` of an object `Y` in an abelian category `C`,
we provide an API in order to construct elements in `Ext X Y n` in terms
of the complex `R.cocomplex` and to make computations in the `Ext`-group.

-/

universe w v u

open CategoryTheory CochainComplex HomComplex Abelian Localization

namespace CategoryTheory.InjectiveResolution

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {X Y : C} (R : InjectiveResolution Y) {n : ℕ}

-- INSTANCE (free from Core): :

noncomputable def extEquivCohomologyClass :
    Ext X Y n ≃ CohomologyClass ((singleFunctor C 0).obj X) R.cochainComplex n :=
  (SmallShiftedHom.postcompEquiv.{w} R.ι'
      (by rw [HomologicalComplex.mem_quasiIso_iff]; infer_instance)).trans
    CochainComplex.HomComplex.CohomologyClass.equivOfIsKInjective.{w}.symm

set_option backward.isDefEq.respectTransparency false in

lemma extEquivCohomologyClass_symm_mk_hom [HasDerivedCategory C]
    (x : Cocycle ((singleFunctor C 0).obj X) R.cochainComplex n) :
    (R.extEquivCohomologyClass.symm (.mk x)).hom =
      (ShiftedHom.mk₀ _ rfl ((DerivedCategory.singleFunctorIsoCompQ C 0).hom.app X)).comp
        ((ShiftedHom.map (Cocycle.equivHomShift.symm x) DerivedCategory.Q).comp
        (.mk₀ _ rfl (inv (DerivedCategory.Q.map R.ι') ≫
          (DerivedCategory.singleFunctorIsoCompQ C 0).inv.app Y)) (zero_add _)) (add_zero _) := by
  change SmallShiftedHom.equiv _ _ ((CohomologyClass.mk x).toSmallShiftedHom.comp _ _) = _
  simp only [SmallShiftedHom.equiv_comp, CohomologyClass.equiv_toSmallShiftedHom_mk,
    SmallShiftedHom.equiv_mk₀Inv, isoOfHom, asIso_inv, Functor.comp_obj,
    DerivedCategory.singleFunctorIsoCompQ, Iso.refl_hom, NatTrans.id_app, Iso.refl_inv,
    ShiftedHom.mk₀_id_comp]
  congr
  cat_disch
