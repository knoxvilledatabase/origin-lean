/-
Extracted from AlgebraicGeometry/Morphisms/IsIso.lean
Genuine: 4 of 6 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!

# Being an isomorphism is local at the target

-/

universe u

open CategoryTheory MorphismProperty

namespace AlgebraicGeometry

lemma isIso_iff_isOpenImmersion_and_surjective {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso f ↔ IsOpenImmersion f ∧ Surjective f := by
  rw [surjective_iff, ← TopCat.epi_iff_surjective, isIso_iff_isOpenImmersion_and_epi_base]

lemma isomorphisms_eq_isOpenImmersion_inf_surjective :
    isomorphisms Scheme = (@IsOpenImmersion ⊓ @Surjective : MorphismProperty Scheme) := by
  ext
  rw [isomorphisms.iff, isIso_iff_isOpenImmersion_and_surjective]
  rfl

lemma isomorphisms_eq_stalkwise :
    isomorphisms Scheme = (isomorphisms TopCat).inverseImage Scheme.forgetToTop ⊓
      stalkwise (fun f ↦ Function.Bijective f) := by
  rw [isomorphisms_eq_isOpenImmersion_inf_surjective, isOpenImmersion_eq_inf,
    surjective_eq_topologically, inf_right_comm]
  congr 1
  ext X Y f
  exact ⟨fun H ↦ inferInstanceAs (IsIso (TopCat.isoOfHomeo
    (H.1.1.toHomeomorphOfSurjective H.2)).hom), fun (_ : IsIso f.base) ↦
    let e := (TopCat.homeoOfIso <| asIso f.base); ⟨e.isOpenEmbedding, e.surjective⟩⟩

example : IsZariskiLocalAtTarget (isomorphisms Scheme) := inferInstance

set_option backward.isDefEq.respectTransparency false in

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

set_option backward.isDefEq.respectTransparency false in

lemma isIso_SpecMap_iff {R S : CommRingCat.{u}} {f : R ⟶ S} :
    IsIso (Spec.map f) ↔ Function.Bijective f.hom := by
  rw [← ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun h ↦ ?_, fun h ↦ inferInstance⟩
  rw [← isomorphisms.iff, (isomorphisms _).arrow_mk_iso_iff (arrowIsoΓSpecOfIsAffine f),
    isomorphisms.iff]
  infer_instance

end AlgebraicGeometry
