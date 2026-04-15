/-
Extracted from CategoryTheory/Sites/CoverLifting.lean
Genuine: 9 of 12 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Cocontinuous functors between sites.

We define cocontinuous functors between sites as functors that pull covering sieves back to
covering sieves. This concept is also known as *cover-lifting* or
*cover-reflecting functors*. We use the original terminology and definition of SGA 4 III 2.1.
However, the notion of cocontinuous functor should not be confused with
the general definition of cocontinuous functors between categories as functors preserving
small colimits.

## Main definitions

* `CategoryTheory.Functor.IsCocontinuous`: a functor between sites is cocontinuous if it
  pulls back covering sieves to covering sieves
* `CategoryTheory.Functor.sheafPushforwardCocontinuous`: A cocontinuous functor
  `G : (C, J) ⥤ (D, K)` induces a functor `Sheaf J A ⥤ Sheaf K A`.

## Main results
* `CategoryTheory.ran_isSheaf_of_isCocontinuous`: If `G : C ⥤ D` is cocontinuous, then
  `G.op.ran` (`ₚu`) as a functor `(Cᵒᵖ ⥤ A) ⥤ (Dᵒᵖ ⥤ A)` of presheaves maps sheaves to sheaves.
* `CategoryTheory.Functor.sheafAdjunctionCocontinuous`: If `G : (C, J) ⥤ (D, K)` is cocontinuous
  and continuous, then `G.sheafPushforwardContinuous A J K` and
  `G.sheafPushforwardCocontinuous A J K` are adjoint.

## References

* [Elephant]: *Sketches of an Elephant*, P. T. Johnstone: C2.3.
* [S. MacLane, I. Moerdijk, *Sheaves in Geometry and Logic*][MM92]
* https://stacks.math.columbia.edu/tag/00XI

-/

universe w' w v v₁ v₂ v₃ u u₁ u₂ u₃

noncomputable section

open CategoryTheory

open Opposite

open CategoryTheory.Presieve.FamilyOfElements

open CategoryTheory.Presieve

open CategoryTheory.Limits

namespace CategoryTheory

section IsCocontinuous

variable {C : Type*} [Category* C] {D : Type*} [Category* D] {E : Type*} [Category* E] (G : C ⥤ D)
  (G' : D ⥤ E)

variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)

variable {L : GrothendieckTopology E}

class Functor.IsCocontinuous : Prop where
  cover_lift : ∀ {U : C} {S : Sieve (G.obj U)} (_ : S ∈ K (G.obj U)), S.functorPullback G ∈ J U

lemma Functor.cover_lift [G.IsCocontinuous J K] {U : C} {S : Sieve (G.obj U)}
    (hS : S ∈ K (G.obj U)) : S.functorPullback G ∈ J U :=
  IsCocontinuous.cover_lift hS

-- INSTANCE (free from Core): isCocontinuous_id

theorem isCocontinuous_comp [G.IsCocontinuous J K] [G'.IsCocontinuous K L] :
    (G ⋙ G').IsCocontinuous J L where
  cover_lift h := G.cover_lift J K (G'.cover_lift K L h)

variable {F : C ⥤ D} {G : D ⥤ C}

set_option backward.isDefEq.respectTransparency false in

lemma Adjunction.isCocontinuous_iff_coverPreserving (adj : F ⊣ G) :
    F.IsCocontinuous J K ↔ CoverPreserving K J G := by
  refine ⟨fun h ↦ ⟨?_⟩, fun h ↦ ⟨?_⟩⟩
  · intro U S hS
    refine J.superset_covering ?_ <| h.cover_lift (K.pullback_stable (adj.counit.app _) hS)
    intro X f hf
    refine ⟨F.obj X, F.map f ≫ adj.counit.app _, adj.unit.app _, hf, by simp⟩
  · intro U S hS
    refine J.superset_covering ?_ (J.pullback_stable (adj.unit.app U) <| h.cover_preserve hS)
    intro X f ⟨Y, g, u, hg, heq⟩
    suffices F.map f = (adj.homEquiv _ _).symm u ≫ g by
      simp [this, S.downward_closed hg]
    simp [← Adjunction.homEquiv_naturality_right_symm, ← heq,
      Adjunction.homEquiv_naturality_left_symm]

lemma Adjunction.isContinuous_of_isCocontinuous (adj : F ⊣ G) [F.IsCocontinuous J K] :
    G.IsContinuous K J := by
  have := adj.isRightAdjoint
  apply Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat J G)
  rwa [← adj.isCocontinuous_iff_coverPreserving]

-- INSTANCE (free from Core): [F.IsCocontinuous

end

end IsCocontinuous

/-!
We will now prove that `G.op.ran : (Cᵒᵖ ⥤ A) ⥤ (Dᵒᵖ ⥤ A)` maps sheaves
to sheaves when `G : C ⥤ D` is a cocontinuous functor.

We do not follow the proofs in SGA 4 III 2.2 or <https://stacks.math.columbia.edu/tag/00XK>.
Instead, we verify as directly as possible that if `F : Cᵒᵖ ⥤ A` is a sheaf,
then `G.op.ran.obj F` is a sheaf. In order to do this, we use the "multifork"
characterization of sheaves which involves limits in the category `A`.
As `G.op.ran.obj F` is the chosen right Kan extension of `F` along `G.op : Cᵒᵖ ⥤ Dᵒᵖ`,
we actually verify that any pointwise right Kan extension of `F` along `G.op` is a sheaf.

-/

variable {C D : Type*} [Category* C] [Category* D] (G : C ⥤ D)

variable {A : Type w} [Category.{w'} A]

variable {J : GrothendieckTopology C} {K : GrothendieckTopology D} [G.IsCocontinuous J K]

namespace RanIsSheafOfIsCocontinuous

variable {G}

variable {F : Cᵒᵖ ⥤ A} (hF : Presheaf.IsSheaf J F)

variable {R : Dᵒᵖ ⥤ A} (α : G.op ⋙ R ⟶ F)

variable (hR : (Functor.RightExtension.mk _ α).IsPointwiseRightKanExtension)

variable {X : D} {S : K.Cover X} (s : Multifork (S.index R))

set_option backward.isDefEq.respectTransparency false in

def liftAux {Y : C} (f : G.obj Y ⟶ X) : s.pt ⟶ F.obj (op Y) :=
  Multifork.IsLimit.lift (hF.isLimitMultifork ⟨_, G.cover_lift J K (K.pullback_stable f S.2)⟩)
    (fun k ↦ s.ι (⟨_, G.map k.f ≫ f, k.hf⟩) ≫ α.app (op k.Y)) (by
      intro { fst := ⟨Y₁, p₁, hp₁⟩, snd := ⟨Y₂, p₂, hp₂⟩, r := ⟨W, g₁, g₂, w⟩ }
      dsimp at g₁ g₂ w ⊢
      simp only [Category.assoc, ← α.naturality, Functor.comp_map,
        Functor.op_map, Quiver.Hom.unop_op]
      apply s.condition_assoc
        { fst.hf := hp₁
          snd.hf := hp₂
          r.g₁ := G.map g₁
          r.g₂ := G.map g₂
          r.w := by simpa using G.congr_map w =≫ f
          .. })

lemma liftAux_map' {Y Y' : C} (f : G.obj Y ⟶ X) (f' : G.obj Y' ⟶ X) {W : C}
    (a : W ⟶ Y) (b : W ⟶ Y') (w : G.map a ≫ f = G.map b ≫ f') :
    liftAux hF α s f ≫ F.map a.op = liftAux hF α s f' ≫ F.map b.op := by
  apply hF.hom_ext ⟨_, G.cover_lift J K (K.pullback_stable (G.map a ≫ f) S.2)⟩
  rintro ⟨T, g, hg⟩
  dsimp
  have eq₁ := liftAux_map hF α s f (g ≫ a) ⟨_, _, hg⟩ (𝟙 _) (by simp)
  have eq₂ := liftAux_map hF α s f' (g ≫ b) ⟨_, _, hg⟩ (𝟙 _) (by simp [w])
  dsimp at eq₁ eq₂
  simp only [Functor.map_comp, Functor.map_id, Category.id_comp] at eq₁ eq₂
  simp only [Category.assoc, eq₁, eq₂]

variable {α}

def lift : s.pt ⟶ R.obj (op X) :=
  (hR (op X)).lift (Cone.mk _
    { app := fun j ↦ liftAux hF α s j.hom.unop
      naturality := fun j j' φ ↦ by
        simpa using liftAux_map' hF α s j'.hom.unop j.hom.unop (𝟙 _) φ.right.unop
          (Quiver.Hom.op_inj (by simpa using (StructuredArrow.w φ).symm)) })

lemma fac' (j : StructuredArrow (op X) G.op) :
    lift hF hR s ≫ R.map j.hom ≫ α.app j.right = liftAux hF α s j.hom.unop := by
  apply IsLimit.fac
