/-
Extracted from AlgebraicGeometry/IdealSheaf/Subscheme.lean
Genuine: 10 of 12 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Subscheme associated to an ideal sheaf

We construct the subscheme associated to an ideal sheaf.

## Main definition
* `AlgebraicGeometry.Scheme.IdealSheafData.subscheme`: The subscheme associated to an ideal sheaf.
* `AlgebraicGeometry.Scheme.IdealSheafData.subschemeι`: The inclusion from the subscheme.
* `AlgebraicGeometry.Scheme.Hom.image`: The scheme-theoretic image of a morphism.
* `AlgebraicGeometry.Scheme.kerAdjunction`:
  The adjunction between taking kernels and taking the associated subscheme.

## Note

Some instances are in `Mathlib/AlgebraicGeometry/Morphisms/ClosedImmersion` and
`Mathlib/AlgebraicGeometry/Morphisms/Separated` because they need more API to prove.

-/

open CategoryTheory TopologicalSpace PrimeSpectrum Limits

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

variable (I : IdealSheafData X)

noncomputable

def glueDataObj (U : X.affineOpens) : Scheme :=
  Spec <| .of <| Γ(X, U) ⧸ I.ideal U

noncomputable

def glueDataObjι (U : X.affineOpens) : I.glueDataObj U ⟶ U.1 :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _)) ≫ U.2.isoSpec.inv

set_option backward.isDefEq.respectTransparency false in

-- INSTANCE (free from Core): (U

lemma glueDataObjι_ι (U : X.affineOpens) : I.glueDataObjι U ≫ U.1.ι =
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _)) ≫ U.2.fromSpec := by
  rw [glueDataObjι, Category.assoc]; rfl

lemma ker_glueDataObjι_appTop (U : X.affineOpens) :
    RingHom.ker (I.glueDataObjι U).appTop.hom = (I.ideal U).comap U.1.topIso.hom.hom := by
  let φ : Γ(X, U) ⟶ CommRingCat.of (Γ(X, U) ⧸ I.ideal U) :=
    CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal U))
  rw [← Ideal.mk_ker (I := I.ideal _)]
  change RingHom.ker (Spec.map φ ≫ _).appTop.hom = (RingHom.ker φ.hom).comap _
  rw [← RingHom.ker_equiv_comp _ (Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv, RingHom.comap_ker,
    RingEquiv.toRingHom_eq_coe, Iso.commRingCatIsoToRingEquiv_toRingHom, ← CommRingCat.hom_comp,
    ← CommRingCat.hom_comp]
  congr 2
  simp only [Scheme.Hom.comp_app, TopologicalSpace.Opens.map_top, Category.assoc,
    Scheme.ΓSpecIso_naturality, Scheme.Opens.topIso_hom]
  rw [← Scheme.Hom.appTop, U.2.isoSpec_inv_appTop, Category.assoc, Iso.inv_hom_id_assoc]
  simp only [Scheme.Opens.topIso_hom]

open scoped Set.Notation in

lemma range_glueDataObjι (U : X.affineOpens) :
    Set.range (I.glueDataObjι U) =
      U.2.isoSpec.inv '' PrimeSpectrum.zeroLocus (I.ideal U) := by
  simp only [glueDataObjι, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  erw [range_comap_of_surjective]
  swap; · exact Ideal.Quotient.mk_surjective
  simp
  rfl

lemma range_glueDataObjι_ι (U : X.affineOpens) :
    Set.range (I.glueDataObjι U ≫ U.1.ι) = X.zeroLocus (U := U) (I.ideal U) ∩ U := by
  simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, range_glueDataObjι]
  rw [← Set.image_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base, IsAffineOpen.isoSpec_inv_ι,
    IsAffineOpen.fromSpec_image_zeroLocus]

noncomputable

def glueDataObjCarrierIso (U : X.affineOpens) :
    (I.glueDataObj U).carrier ≅ TopCat.of ↑(X.zeroLocus (U := U) (I.ideal U) ∩ U) :=
  TopCat.isoOfHomeo ((I.glueDataObjι U ≫ U.1.ι).isEmbedding.toHomeomorph.trans
    (.setCongr (I.range_glueDataObjι_ι U)))

noncomputable

def glueDataObjMap {U V : X.affineOpens} (h : U ≤ V) : I.glueDataObj U ⟶ I.glueDataObj V :=
  Spec.map (CommRingCat.ofHom (Ideal.quotientMap _ _ (I.ideal_le_comap_ideal h)))

lemma isLocalization_away {U V : X.affineOpens}
    (h : U ≤ V) (f : Γ(X, V.1)) (hU : U = X.affineBasicOpen f) :
      letI := (Ideal.quotientMap _ _ (I.ideal_le_comap_ideal h)).toAlgebra
      IsLocalization.Away (Ideal.Quotient.mk (I.ideal V) f) (Γ(X, U) ⧸ (I.ideal U)) := by
  letI := (Ideal.quotientMap _ _ (I.ideal_le_comap_ideal h)).toAlgebra
  letI := (X.presheaf.map (homOfLE (X := X.Opens) h).op).hom.toAlgebra
  have : IsLocalization.Away f Γ(X, U) := by
    subst hU; exact V.2.isLocalization_of_eq_basicOpen _ _ rfl
  simp only [IsLocalization.Away, ← Submonoid.map_powers]
  refine IsLocalization.of_surjective _ _ _ Ideal.Quotient.mk_surjective _
    Ideal.Quotient.mk_surjective ?_ ?_
  · simp [RingHom.algebraMap_toAlgebra, Ideal.quotientMap_comp_mk]; rfl
  · simp only [Ideal.mk_ker, RingHom.algebraMap_toAlgebra, I.map_ideal', le_refl]

-- INSTANCE (free from Core): isOpenImmersion_glueDataObjMap

lemma opensRange_glueDataObjMap {V : X.affineOpens} (f : Γ(X, V.1)) :
      (I.glueDataObjMap (X.affineBasicOpen_le f)).opensRange =
        (I.glueDataObjι V) ⁻¹ᵁ (V.1.ι ⁻¹ᵁ X.basicOpen f) := by
  letI := (Ideal.quotientMap _ _ (I.ideal_le_comap_ideal (X.affineBasicOpen_le f))).toAlgebra
  let f' : Γ(X, V) ⧸ I.ideal V := Ideal.Quotient.mk _ f
  have := I.isLocalization_away (X.affineBasicOpen_le f) f rfl
  ext1
  refine (localization_away_comap_range _ f').trans ?_
  rw [← comap_basicOpen, ← V.2.fromSpec_preimage_basicOpen,
    ← Scheme.Hom.comp_preimage, glueDataObjι_ι]
  rfl

set_option backward.isDefEq.respectTransparency false in
