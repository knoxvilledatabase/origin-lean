/-
Extracted from CategoryTheory/Sites/Coherent/RegularSheaves.lean
Genuine: 7 of 7 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Sheaves for the regular topology

This file characterises sheaves for the regular topology.

## Main results

* `equalizerCondition_iff_isSheaf`: In a preregular category with pullbacks, the sheaves for the
  regular topology are precisely the presheaves satisfying an equaliser condition with respect to
  effective epimorphisms.

* `isSheaf_of_projective`: In a preregular category in which every object is projective, every
  presheaf is a sheaf for the regular topology.
-/

namespace CategoryTheory

open Limits

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]

open Opposite Presieve Functor

class Presieve.regular {X : C} (R : Presieve X) : Prop where
  /-- `R` consists of a single epimorphism. -/
  single_epi : ∃ (Y : C) (f : Y ⟶ X), R = Presieve.ofArrows (fun (_ : Unit) ↦ Y)
    (fun (_ : Unit) ↦ f) ∧ EffectiveEpi f

namespace regularTopology

lemma equalizerCondition_w (P : Cᵒᵖ ⥤ D) {X B : C} {π : X ⟶ B} (c : PullbackCone π π) :
    P.map π.op ≫ P.map c.fst.op = P.map π.op ≫ P.map c.snd.op := by
  simp only [← Functor.map_comp, ← op_comp, c.condition]

def SingleEqualizerCondition (P : Cᵒᵖ ⥤ D) ⦃X B : C⦄ (π : X ⟶ B) : Prop :=
  ∀ (c : PullbackCone π π) (_ : IsLimit c),
    Nonempty (IsLimit (Fork.ofι (P.map π.op) (equalizerCondition_w P c)))

def EqualizerCondition (P : Cᵒᵖ ⥤ D) : Prop :=
  ∀ ⦃X B : C⦄ (π : X ⟶ B) [EffectiveEpi π], SingleEqualizerCondition P π

theorem equalizerCondition_of_natIso {P P' : Cᵒᵖ ⥤ D} (i : P ≅ P')
    (hP : EqualizerCondition P) : EqualizerCondition P' := fun X B π _ c hc ↦
  ⟨Fork.isLimitOfIsos _ (hP π c hc).some _ (i.app _) (i.app _) (i.app _)⟩

set_option backward.isDefEq.respectTransparency false in

theorem equalizerCondition_precomp_of_preservesPullback (P : Cᵒᵖ ⥤ D) (F : E ⥤ C)
    [∀ {X B} (π : X ⟶ B) [EffectiveEpi π], PreservesLimit (cospan π π) F]
    [F.PreservesEffectiveEpis] (hP : EqualizerCondition P) : EqualizerCondition (F.op ⋙ P) := by
  intro X B π _ c hc
  have h : P.map (F.map π).op = (F.op ⋙ P).map π.op := by simp
  refine ⟨(IsLimit.equivIsoLimit (ForkOfι.ext ?_ _ h)) ?_⟩
  · simp only [Functor.comp_map, op_map, Quiver.Hom.unop_op, ← map_comp, ← op_comp, c.condition]
  · refine (hP (F.map π) (PullbackCone.mk (F.map c.fst) (F.map c.snd) ?_) ?_).some
    · simp only [← map_comp, c.condition]
    · exact (isLimitMapConePullbackConeEquiv F c.condition)
        (isLimitOfPreserves F (hc.ofIsoLimit (PullbackCone.ext (Iso.refl _) (by simp) (by simp))))

def mapToEqualizer (P : Cᵒᵖ ⥤ Type*) {W X B : C} (f : X ⟶ B)
    (g₁ g₂ : W ⟶ X) (w : g₁ ≫ f = g₂ ≫ f) :
    P.obj (op B) ⟶ { x : P.obj (op X) | P.map g₁.op x = P.map g₂.op x } :=
  TypeCat.ofHom fun t ↦
    ⟨P.map f.op t, by simp only [Set.mem_setOf_eq, ← comp_apply, ← Functor.map_comp, ← op_comp, w]⟩
