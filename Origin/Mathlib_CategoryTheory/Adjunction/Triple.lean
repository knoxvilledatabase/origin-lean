/-
Extracted from CategoryTheory/Adjunction/Triple.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Adjoint triples

This file concerns adjoint triples `F ⊣ G ⊣ H` of functors `F H : C ⥤ D`, `G : D ⥤ C`. We first
prove that `F` is fully faithful iff `H` is, and then prove results about the two special cases
where `G` is fully faithful or `F` and `H` are.

## Main results

All results are about an adjoint triple `F ⊣ G ⊣ H` where `adj₁ : F ⊣ G` and `adj₂ : G ⊣ H`. We
bundle the adjunctions in a structure `Triple F G H`.
* `fullyFaithfulEquiv`: `F` is fully faithful iff `H` is.
* `rightToLeft`: the canonical natural transformation `H ⟶ F` that exists whenever `G` is fully
  faithful. This is defined as the preimage of `adj₂.counit ≫ adj₁.unit` under whiskering with `G`,
  but formulas in terms of the units resp. counits of the adjunctions are also given.
* `whiskerRight_rightToLeft`: whiskering `rightToLeft : H ⟶ F` with `G` yields
  `adj₂.counit ≫ adj₁.unit : H ⋙ G ⟶ F ⋙ G`.
* `epi_rightToLeft_app_iff_epi_map_adj₁_unit_app`: `rightToLeft : H ⟶ F` is epic at `X` iff the
  image of `adj₁.unit.app X` under `H` is.
* `epi_rightToLeft_app_iff_epi_map_adj₂_counit_app`: `rightToLeft : H ⟶ F` is epic at `X` iff the
  image of `adj₂.counit.app X` under `F` is.
* `epi_rightToLeft_app_iff`: when `H` preserves epimorphisms, `rightToLeft : H ⟶ F` is epic at `X`
  iff `adj₂.counit ≫ adj₁.unit : H ⋙ G ⟶ F ⋙ G` is.
* `leftToRight`: the canonical natural transformation `F ⟶ H` that exists whenever `F` and `H` are
  fully faithful. This is defined in terms of the units of the adjunctions, but a formula in terms
  of the counits is also given.
* `whiskerLeft_leftToRight`: whiskering `G` with `leftToRight : F ⟶ H` yields
  `adj₁.counit ≫ adj₂.unit : G ⋙ F ⟶ G ⋙ H`.
* `mono_leftToRight_app_iff_mono_adj₂_unit_app`: `leftToRight : F ⟶ H` is monic at `X` iff
  `adj₂.unit` is monic at `F.obj X`.
* `mono_leftToRight_app_iff_mono_adj₁_counit_app`: `leftToRight : F ⟶ H` is monic at `X` iff
  `adj₁.counit` is monic at `H.obj X`.
* `mono_leftToRight_app_iff`: `leftToRight : F ⟶ H` is componentwise monic iff
  `adj₁.counit ≫ adj₂.unit : G ⋙ F ⟶ G ⋙ H` is.
-/

open CategoryTheory Functor

variable {C D : Type*} [Category* C] [Category* D]

variable (F : C ⥤ D) (G : D ⥤ C) (H : C ⥤ D)

structure CategoryTheory.Adjunction.Triple where
  /-- Adjunction `F ⊣ G` of the adjoint triple `F ⊣ G ⊣ H`. -/
  adj₁ : F ⊣ G
  /-- Adjunction `G ⊣ H` of the adjoint triple `F ⊣ G ⊣ H`. -/
  adj₂ : G ⊣ H

namespace CategoryTheory.Adjunction.Triple

variable {F G H} (t : Triple F G H)

lemma isIso_unit_iff_isIso_counit : IsIso t.adj₁.unit ↔ IsIso t.adj₂.counit := by
  let adj : F ⋙ G ⊣ H ⋙ G := t.adj₁.comp t.adj₂
  constructor
  · intro h
    let idAdj : 𝟭 C ⊣ H ⋙ G := adj.ofNatIsoLeft (asIso t.adj₁.unit).symm
    exact t.adj₂.isIso_counit_of_iso (idAdj.rightAdjointUniq id)
  · intro h
    let adjId : F ⋙ G ⊣ 𝟭 C := adj.ofNatIsoRight (asIso t.adj₂.counit)
    exact t.adj₁.isIso_unit_of_iso (adjId.leftAdjointUniq id)

noncomputable def fullyFaithfulEquiv : F.FullyFaithful ≃ H.FullyFaithful where
  toFun h :=
    haveI := h.full
    haveI := h.faithful
    haveI : IsIso t.adj₂.counit := by
      rw [← t.isIso_unit_iff_isIso_counit]
      infer_instance
    t.adj₂.fullyFaithfulROfIsIsoCounit
  invFun h :=
    haveI := h.full
    haveI := h.faithful
    haveI : IsIso t.adj₁.unit := by
      rw [t.isIso_unit_iff_isIso_counit]
      infer_instance
    t.adj₁.fullyFaithfulLOfIsIsoUnit
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
