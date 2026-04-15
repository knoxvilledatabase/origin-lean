/-
Extracted from CategoryTheory/Abelian/GrothendieckAxioms/Basic.lean
Genuine: 10 of 10 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Grothendieck Axioms

This file defines some of the Grothendieck Axioms for abelian categories, and proves
basic facts about them.

## Definitions

- `HasExactColimitsOfShape J C` -- colimits of shape `J` in `C` are exact.
- The dual of the above definitions, called `HasExactLimitsOfShape`.
- `AB4` -- coproducts are exact (this is formulated in terms of `HasExactColimitsOfShape`).
- `AB5` -- filtered colimits are exact (this is formulated in terms of `HasExactColimitsOfShape`).

## Theorems

- The implication from `AB5` to `AB4` is established in `AB4.ofAB5`.
- That `HasExactColimitsOfShape J C` is invariant under equivalences in both parameters is shown
  in `HasExactColimitsOfShape.of_domain_equivalence` and
  `HasExactColimitsOfShape.of_codomain_equivalence`.

## Remarks

For `AB4` and `AB5`, we only require left exactness as right exactness is automatic.
A comparison with Grothendieck's original formulation of the properties can be found in the
comments of the linked Stacks page.
Exactness as the preservation of short exact sequences is introduced in
`Mathlib/CategoryTheory/Abelian/Exact.lean`.

We do not require `Abelian` in the definition of `AB4` and `AB5` because these classes represent
individual axioms. An `AB4` category is an _abelian_ category satisfying `AB4`, and similarly for
`AB5`.

## References
* [Stacks: Grothendieck's AB conditions](https://stacks.math.columbia.edu/tag/079A)

-/

namespace CategoryTheory

open Limits Functor

attribute [instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

universe w w' w₂ w₂' v v' v'' u u' u''

variable (C : Type u) [Category.{v} C]

class HasExactColimitsOfShape (J : Type u') [Category.{v'} J] (C : Type u) [Category.{v} C]
    [HasColimitsOfShape J C] where
  /-- Exactness of `J`-shaped colimits stated as `colim : (J ⥤ C) ⥤ C` preserving finite limits. -/
  preservesFiniteLimits : PreservesFiniteLimits (colim (J := J) (C := C))

class HasExactLimitsOfShape (J : Type u') [Category.{v'} J] (C : Type u) [Category.{v} C]
    [HasLimitsOfShape J C] where
  /-- Exactness of `J`-shaped limits stated as `lim : (J ⥤ C) ⥤ C` preserving finite colimits. -/
  preservesFiniteColimits : PreservesFiniteColimits (lim (J := J) (C := C))

attribute [instance] HasExactColimitsOfShape.preservesFiniteLimits

  HasExactLimitsOfShape.preservesFiniteColimits

variable {C} in

lemma HasExactColimitsOfShape.domain_of_functor {D : Type*} (J : Type*) [Category* J] [Category* D]
    [HasColimitsOfShape J C] [HasColimitsOfShape J D] [HasExactColimitsOfShape J D]
    (F : C ⥤ D) [PreservesFiniteLimits F] [ReflectsFiniteLimits F] [HasFiniteLimits C]
    [PreservesColimitsOfShape J F] : HasExactColimitsOfShape J C where
  preservesFiniteLimits := { preservesFiniteLimits I := { preservesLimit {G} := {
    preserves {c} hc := by
      constructor
      apply isLimitOfReflects F
      refine (IsLimit.equivOfNatIsoOfIso (isoWhiskerLeft G (preservesColimitNatIso F).symm)
        ((_ ⋙ colim).mapCone c) _ ?_) (isLimitOfPreserves _ hc)
      exact Cone.ext ((preservesColimitNatIso F).symm.app _)
        fun i ↦ (preservesColimitNatIso F).inv.naturality _ } } }

variable {C} in

lemma HasExactLimitsOfShape.domain_of_functor {D : Type*} (J : Type*) [Category* D] [Category* J]
    [HasLimitsOfShape J C] [HasLimitsOfShape J D] [HasExactLimitsOfShape J D]
    (F : C ⥤ D) [PreservesFiniteColimits F] [ReflectsFiniteColimits F] [HasFiniteColimits C]
    [PreservesLimitsOfShape J F] : HasExactLimitsOfShape J C where
  preservesFiniteColimits := { preservesFiniteColimits I := { preservesColimit {G} := {
    preserves {c} hc := by
      constructor
      apply isColimitOfReflects F
      refine (IsColimit.equivOfNatIsoOfIso (isoWhiskerLeft G (preservesLimitNatIso F).symm)
        ((_ ⋙ lim).mapCocone c) _ ?_) (isColimitOfPreserves _ hc)
      refine Cocone.ext ((preservesLimitNatIso F).symm.app _) fun i ↦ ?_
      simp only [Functor.comp_obj, lim_obj, Functor.mapCocone_pt, isoWhiskerLeft_inv, Iso.symm_inv,
        Cocone.precompose_obj_pt, whiskeringRight_obj_obj, Functor.const_obj_obj,
        Cocone.precompose_obj_ι, NatTrans.comp_app, whiskerLeft_app, preservesLimitNatIso_hom_app,
        Functor.mapCocone_ι_app, Functor.comp_map, whiskeringRight_obj_map, lim_map, Iso.app_hom,
        Iso.symm_hom, preservesLimitNatIso_inv_app, Category.assoc]
      rw [← Iso.eq_inv_comp]
      exact (preservesLimitNatIso F).inv.naturality _ } } }

lemma HasExactColimitsOfShape.of_domain_equivalence {J J' : Type*} [Category* J] [Category* J']
    (e : J ≌ J') [HasColimitsOfShape J C] [HasExactColimitsOfShape J C] :
    haveI : HasColimitsOfShape J' C := hasColimitsOfShape_of_equivalence e
    HasExactColimitsOfShape J' C :=
  haveI : HasColimitsOfShape J' C := hasColimitsOfShape_of_equivalence e
  ⟨preservesFiniteLimits_of_natIso (Functor.Final.colimIso e.functor)⟩

variable {C} in

lemma HasExactColimitsOfShape.of_codomain_equivalence (J : Type*) [Category* J] {D : Type*}
    [Category* D] (e : C ≌ D) [HasColimitsOfShape J C] [HasExactColimitsOfShape J C] :
    haveI : HasColimitsOfShape J D := Adjunction.hasColimitsOfShape_of_equivalence e.inverse
    HasExactColimitsOfShape J D := by
  haveI : HasColimitsOfShape J D := Adjunction.hasColimitsOfShape_of_equivalence e.inverse
  refine ⟨⟨fun _ _ _ => ⟨@fun K => ?_⟩⟩⟩
  refine preservesLimit_of_natIso K (?_ : e.congrRight.inverse ⋙ colim ⋙ e.functor ≅ colim)
  apply e.symm.congrRight.fullyFaithfulFunctor.preimageIso
  exact isoWhiskerLeft (_ ⋙ colim) e.unitIso.symm ≪≫ (preservesColimitNatIso e.inverse).symm

lemma HasExactLimitsOfShape.of_domain_equivalence {J J' : Type*} [Category* J] [Category* J']
    (e : J ≌ J') [HasLimitsOfShape J C] [HasExactLimitsOfShape J C] :
    haveI : HasLimitsOfShape J' C := hasLimitsOfShape_of_equivalence e
    HasExactLimitsOfShape J' C :=
  haveI : HasLimitsOfShape J' C := hasLimitsOfShape_of_equivalence e
  ⟨preservesFiniteColimits_of_natIso (Functor.Initial.limIso e.functor)⟩

variable {C} in

lemma HasExactLimitsOfShape.of_codomain_equivalence (J : Type*) [Category* J] {D : Type*}
    [Category* D] (e : C ≌ D) [HasLimitsOfShape J C] [HasExactLimitsOfShape J C] :
    haveI : HasLimitsOfShape J D := Adjunction.hasLimitsOfShape_of_equivalence e.inverse
    HasExactLimitsOfShape J D := by
  haveI : HasLimitsOfShape J D := Adjunction.hasLimitsOfShape_of_equivalence e.inverse
  refine ⟨⟨fun _ _ _ => ⟨@fun K => ?_⟩⟩⟩
  refine preservesColimit_of_natIso K (?_ : e.congrRight.inverse ⋙ lim ⋙ e.functor ≅ lim)
  apply e.symm.congrRight.fullyFaithfulFunctor.preimageIso
  exact isoWhiskerLeft (_ ⋙ lim) e.unitIso.symm ≪≫ (preservesLimitNatIso e.inverse).symm

namespace Adjunction

variable {C} {D : Type u''} [Category.{v''} D] {F : C ⥤ D} {G : D ⥤ C}

lemma hasExactColimitsOfShape (adj : F ⊣ G) [G.Full] [G.Faithful]
    (J : Type u') [Category.{v'} J] [HasColimitsOfShape J C] [HasColimitsOfShape J D]
    [HasExactColimitsOfShape J C] [HasFiniteLimits D] [PreservesFiniteLimits F] :
    HasExactColimitsOfShape J D where
  preservesFiniteLimits := ⟨fun K _ _ ↦ ⟨fun {H} ↦ by
    have : PreservesLimitsOfSize.{0, 0} G := adj.rightAdjoint_preservesLimits
    have : PreservesColimitsOfSize.{v', u'} F := adj.leftAdjoint_preservesColimits
    let e : (whiskeringRight J D C).obj G ⋙ colim ⋙ F ≅ colim :=
      isoWhiskerLeft _ (preservesColimitNatIso F) ≪≫ (Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight (whiskeringRightObjCompIso G F) _ ≪≫
        isoWhiskerRight ((whiskeringRight J D D).mapIso (asIso adj.counit)) _ ≪≫
        isoWhiskerRight whiskeringRightObjIdIso _ ≪≫ colim.leftUnitor
    exact preservesLimit_of_natIso _ e⟩⟩

lemma hasExactLimitsOfShape (adj : F ⊣ G) [F.Full] [F.Faithful]
    (J : Type u') [Category.{v'} J] [HasLimitsOfShape J C] [HasLimitsOfShape J D]
    [HasExactLimitsOfShape J D] [HasFiniteColimits C] [PreservesFiniteColimits G] :
    HasExactLimitsOfShape J C where
  preservesFiniteColimits := ⟨fun K _ _ ↦ ⟨fun {H} ↦ by
    have : PreservesLimitsOfSize.{v', u'} G := adj.rightAdjoint_preservesLimits
    have : PreservesColimitsOfSize.{0, 0} F := adj.leftAdjoint_preservesColimits
    let e : (whiskeringRight J _ _).obj F ⋙ lim ⋙ G ≅ lim :=
      isoWhiskerLeft _ (preservesLimitNatIso G) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight (whiskeringRightObjCompIso F G) _ ≪≫
        isoWhiskerRight ((whiskeringRight J C C).mapIso (asIso adj.unit).symm) _ ≪≫
        isoWhiskerRight whiskeringRightObjIdIso _ ≪≫ lim.leftUnitor
    exact preservesColimit_of_natIso _ e⟩⟩

end Adjunction
