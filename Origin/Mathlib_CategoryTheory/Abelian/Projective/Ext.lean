/-
Extracted from CategoryTheory/Abelian/Projective/Ext.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Computing `Ext` using a projective resolution

Given a projective resolution `R` of an object `X` in an abelian category `C`,
we provide an API in order to construct elements in `Ext X Y n` in terms
of the complex `R.complex` and to make computations in the `Ext`-group.

## TODO
* Functoriality in `X`: this would involve a morphism `X ⟶ X'`, projective
  resolutions `R` and `R'` of `X` and `X'`, a lift of `X ⟶ X'` as a morphism
  of cochain complexes `R.complex ⟶ R'.complex`; in this context,
  we should be able to compute the precomposition of an element
  `R.extMk f m hm hf : Ext X' Y n` by `X ⟶ X'`.

-/

universe w v u

open CategoryTheory CochainComplex HomComplex Abelian Localization

namespace CategoryTheory.ProjectiveResolution

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {X Y : C} (R : ProjectiveResolution X) {n : ℕ}

-- INSTANCE (free from Core): :

noncomputable def extEquivCohomologyClass :
    Ext X Y n ≃ CohomologyClass R.cochainComplex ((singleFunctor C 0).obj Y) n :=
  (SmallShiftedHom.precompEquiv.{w} R.π'
    ((by rw [HomologicalComplex.mem_quasiIso_iff]; infer_instance))).trans
      CochainComplex.HomComplex.CohomologyClass.equivOfIsKProjective.{w}.symm

set_option backward.isDefEq.respectTransparency false in

lemma extEquivCohomologyClass_symm_mk_hom [HasDerivedCategory C]
    (x : Cocycle R.cochainComplex ((singleFunctor C 0).obj Y) n) :
    (R.extEquivCohomologyClass.symm (.mk x)).hom =
    (ShiftedHom.mk₀ _ rfl ((DerivedCategory.singleFunctorIsoCompQ C 0).hom.app X ≫
      inv (DerivedCategory.Q.map R.π'))).comp
        ((ShiftedHom.map (Cocycle.equivHomShift.symm x) DerivedCategory.Q).comp
          (.mk₀ _ rfl ((DerivedCategory.singleFunctorIsoCompQ C 0).inv.app Y))
            (zero_add _)) (add_zero _) := by
  change SmallShiftedHom.equiv _ _ (.comp _ (CohomologyClass.mk x).toSmallShiftedHom _) = _
  simp only [SmallShiftedHom.equiv_comp, SmallShiftedHom.equiv_mk₀Inv, isoOfHom, asIso_inv,
    CohomologyClass.equiv_toSmallShiftedHom_mk, Functor.comp_obj,
    DerivedCategory.singleFunctorIsoCompQ, Iso.refl_hom, NatTrans.id_app, Category.id_comp,
    Iso.refl_inv]
  congr
  exact (ShiftedHom.comp_mk₀_id ..).symm
