/-
Extracted from CategoryTheory/Functor/KanExtension/Preserves.lean
Genuine: 8 of 8 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Preservation of Kan extensions

Given functors `F : A ⥤ B`, `L : B ⥤ C`, and `G : B ⥤ D`,
we introduce a typeclass `G.PreservesLeftKanExtension F L` which encodes the fact that
the left Kan extension of `F` along `L` is preserved by the functor `G`.

When the Kan extension is pointwise, it suffices that `G` preserves (co)limits of the relevant
diagrams.

We introduce the dual typeclass `G.PreservesRightKanExtension`.

-/

namespace CategoryTheory.Functor

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  (G : B ⥤ D) (F : A ⥤ B) (L : A ⥤ C)

noncomputable section

section LeftKanExtension

class PreservesLeftKanExtension where
  preserves : ∀ (F' : C ⥤ B) (α : F ⟶ L ⋙ F') [IsLeftKanExtension F' α],
    IsLeftKanExtension (F' ⋙ G) <| whiskerRight α G ≫ (Functor.associator _ _ _).hom

lemma PreservesLeftKanExtension.mk'
    (preserves : ∀ {E : LeftExtension L F}, E.IsUniversal →
      Nonempty (LeftExtension.postcompose₂ L F G |>.obj E).IsUniversal) :
    G.PreservesLeftKanExtension F L where
  preserves _ _ h :=
    ⟨⟨Limits.IsInitial.equivOfIso
        (LeftExtension.postcompose₂ObjMkIso _ _) <| (preserves h.nonempty_isUniversal.some).some⟩⟩

set_option backward.isDefEq.respectTransparency false in

lemma PreservesLeftKanExtension.mk_of_preserves_isLeftKanExtension
    (F' : C ⥤ B) (α : F ⟶ L ⋙ F') [IsLeftKanExtension F' α]
    (h : IsLeftKanExtension (F' ⋙ G) <| whiskerRight α G ≫ (Functor.associator _ _ _).hom) :
    G.PreservesLeftKanExtension F L :=
  .mk fun F'' α' h ↦
    isLeftKanExtension_of_iso
      (isoWhiskerRight (leftKanExtensionUnique F' α F'' α') G)
      (whiskerRight α G ≫ (Functor.associator _ _ _).hom)
      (whiskerRight α' G ≫ (Functor.associator _ _ _).hom)
      (by ext x; simp [← G.map_comp])

lemma PreservesLeftKanExtension.mk_of_preserves_isUniversal (E : LeftExtension L F)
    (hE : E.IsUniversal) (h : Nonempty (LeftExtension.postcompose₂ L F G |>.obj E).IsUniversal) :
    G.PreservesLeftKanExtension F L :=
  .mk' G F L fun hE' ↦
    ⟨Limits.IsInitial.equivOfIso
      (LeftExtension.postcompose₂ L F G|>.mapIso <| Limits.IsInitial.uniqueUpToIso hE hE') h.some⟩

attribute [instance] PreservesLeftKanExtension.preserves

class PreservesPointwiseLeftKanExtensionAt (c : C) where
  /-- `G` preserves every pointwise extensions of `F` along `L` at `c`. -/
  preserves : ∀ (E : LeftExtension L F), E.IsPointwiseLeftKanExtensionAt c →
    Nonempty ((LeftExtension.postcompose₂ L F G |>.obj E).IsPointwiseLeftKanExtensionAt c)

abbrev PreservesPointwiseLeftKanExtension := ∀ c : C, PreservesPointwiseLeftKanExtensionAt G F L c

variable {F L} in

def LeftExtension.IsPointwiseLeftKanExtensionAt.postcompose {c : C}
    [PreservesPointwiseLeftKanExtensionAt G F L c]
    {E : LeftExtension L F} (hE : E.IsPointwiseLeftKanExtensionAt c) :
    LeftExtension.postcompose₂ L F G |>.obj E |>.IsPointwiseLeftKanExtensionAt c :=
  PreservesPointwiseLeftKanExtensionAt.preserves E hE |>.some

variable {F L} in

def LeftExtension.IsPointwiseLeftKanExtension.postcompose
    [PreservesPointwiseLeftKanExtension G F L]
    {E : LeftExtension L F} (hE : E.IsPointwiseLeftKanExtension) :
    LeftExtension.postcompose₂ L F G |>.obj E |>.IsPointwiseLeftKanExtension := fun c ↦
  (hE c).postcompose G
