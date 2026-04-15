/-
Extracted from CategoryTheory/Localization/Triangulated.lean
Genuine: 7 of 8 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-! # Localization of triangulated categories

If `L : C ⥤ D` is a localization functor for a class of morphisms `W` that is compatible
with the triangulation on the category `C` and admits a left calculus of fractions,
it is shown in this file that `D` can be equipped with a pretriangulated category structure,
and that it is triangulated.

## References
* [Jean-Louis Verdier, *Des catégories dérivées des catégories abéliennes*][verdier1996]

-/

assert_not_exists TwoSidedIdeal

namespace CategoryTheory

open Category Limits Pretriangulated Localization

variable {C D : Type*} [Category* C] [Category* D] (L : C ⥤ D)
  [HasShift C ℤ] [Preadditive C] [HasZeroObject C]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]
  [HasShift D ℤ] [L.CommShift ℤ]

namespace MorphismProperty

class IsCompatibleWithTriangulation (W : MorphismProperty C) : Prop
    extends W.IsCompatibleWithShift ℤ where
  compatible_with_triangulation (T₁ T₂ : Triangle C)
    (_ : T₁ ∈ distTriang C) (_ : T₂ ∈ distTriang C)
    (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂) (_ : W a) (_ : W b)
    (_ : T₁.mor₁ ≫ b = a ≫ T₂.mor₁) :
      ∃ (c : T₁.obj₃ ⟶ T₂.obj₃) (_ : W c),
        (T₁.mor₂ ≫ c = b ≫ T₂.mor₂) ∧ (T₁.mor₃ ≫ a⟦1⟧' = c ≫ T₂.mor₃)

export IsCompatibleWithTriangulation (compatible_with_triangulation)

end MorphismProperty

namespace Functor

def essImageDistTriang : Set (Triangle D) :=
  {T | ∃ (T' : Triangle C) (_ : T ≅ L.mapTriangle.obj T'), T' ∈ distTriang C}

lemma contractible_mem_essImageDistTriang [EssSurj L] [HasZeroObject D]
    [HasZeroMorphisms D] [L.PreservesZeroMorphisms] (X : D) :
    contractibleTriangle X ∈ L.essImageDistTriang := by
  refine ⟨contractibleTriangle (L.objPreimage X), ?_, contractible_distinguished _⟩
  exact ((contractibleTriangleFunctor D).mapIso (L.objObjPreimageIso X)).symm ≪≫
    Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) L.mapZeroObject.symm (by simp) (by simp) (by simp)

lemma rotate_essImageDistTriang [Preadditive D] [L.Additive]
    [∀ (n : ℤ), (shiftFunctor D n).Additive] (T : Triangle D) :
    T ∈ L.essImageDistTriang ↔ T.rotate ∈ L.essImageDistTriang := by
  constructor
  · rintro ⟨T', e', hT'⟩
    exact ⟨T'.rotate, (rotate D).mapIso e' ≪≫ L.mapTriangleRotateIso.app T',
      rot_of_distTriang T' hT'⟩
  · rintro ⟨T', e', hT'⟩
    exact ⟨T'.invRotate, (triangleRotation D).unitIso.app T ≪≫ (invRotate D).mapIso e' ≪≫
      L.mapTriangleInvRotateIso.app T', inv_rot_of_distTriang T' hT'⟩

set_option backward.isDefEq.respectTransparency false in

lemma complete_distinguished_essImageDistTriang_morphism
    (H : ∀ (T₁' T₂' : Triangle C) (_ : T₁' ∈ distTriang C) (_ : T₂' ∈ distTriang C)
      (a : L.obj (T₁'.obj₁) ⟶ L.obj (T₂'.obj₁)) (b : L.obj (T₁'.obj₂) ⟶ L.obj (T₂'.obj₂))
      (_ : L.map T₁'.mor₁ ≫ b = a ≫ L.map T₂'.mor₁),
      ∃ (φ : L.mapTriangle.obj T₁' ⟶ L.mapTriangle.obj T₂'), φ.hom₁ = a ∧ φ.hom₂ = b)
    (T₁ T₂ : Triangle D)
    (hT₁ : T₁ ∈ Functor.essImageDistTriang L) (hT₂ : T₂ ∈ L.essImageDistTriang)
    (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂) (fac : T₁.mor₁ ≫ b = a ≫ T₂.mor₁) :
    ∃ c, T₁.mor₂ ≫ c = b ≫ T₂.mor₂ ∧ T₁.mor₃ ≫ a⟦1⟧' = c ≫ T₂.mor₃ := by
  obtain ⟨T₁', e₁, hT₁'⟩ := hT₁
  obtain ⟨T₂', e₂, hT₂'⟩ := hT₂
  have comm₁ := e₁.inv.comm₁
  have comm₁' := e₂.hom.comm₁
  have comm₂ := e₁.hom.comm₂
  have comm₂' := e₂.hom.comm₂
  have comm₃ := e₁.inv.comm₃
  have comm₃' := e₂.hom.comm₃
  dsimp at comm₁ comm₁' comm₂ comm₂' comm₃ comm₃'
  simp only [assoc] at comm₃
  obtain ⟨φ, hφ₁, hφ₂⟩ := H T₁' T₂' hT₁' hT₂' (e₁.inv.hom₁ ≫ a ≫ e₂.hom.hom₁)
    (e₁.inv.hom₂ ≫ b ≫ e₂.hom.hom₂)
    (by simp only [assoc, ← comm₁', ← reassoc_of% fac, ← reassoc_of% comm₁])
  have h₂ := φ.comm₂
  have h₃ := φ.comm₃
  dsimp at h₂ h₃
  simp only [assoc] at h₃
  refine ⟨e₁.hom.hom₃ ≫ φ.hom₃ ≫ e₂.inv.hom₃, ?_, ?_⟩
  · rw [reassoc_of% comm₂, reassoc_of% h₂, hφ₂, assoc, assoc,
      Iso.hom_inv_id_triangle_hom₂_assoc, ← reassoc_of% comm₂',
      Iso.hom_inv_id_triangle_hom₃, comp_id]
  · rw [assoc, assoc, ← cancel_epi e₁.inv.hom₃, ← reassoc_of% comm₃,
      Iso.inv_hom_id_triangle_hom₃_assoc, ← cancel_mono (e₂.hom.hom₁⟦(1 : ℤ)⟧'),
      assoc, assoc, assoc, assoc, assoc, ← Functor.map_comp, ← Functor.map_comp, ← hφ₁,
      h₃, comm₃', Iso.inv_hom_id_triangle_hom₃_assoc]

end Functor

namespace Triangulated

namespace Localization

variable (W : MorphismProperty C) [L.IsLocalization W]
  [W.HasLeftCalculusOfFractions]

set_option backward.isDefEq.respectTransparency false in

include W in

lemma distinguished_cocone_triangle {X Y : D} (f : X ⟶ Y) :
    ∃ (Z : D) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ L.essImageDistTriang := by
  have := essSurj_mapArrow L W
  obtain ⟨φ, ⟨e⟩⟩ : ∃ (φ : Arrow C), Nonempty (L.mapArrow.obj φ ≅ Arrow.mk f) :=
    ⟨_, ⟨Functor.objObjPreimageIso _ _⟩⟩
  obtain ⟨Z, g, h, H⟩ := Pretriangulated.distinguished_cocone_triangle φ.hom
  refine ⟨L.obj Z, e.inv.right ≫ L.map g,
    L.map h ≫ (L.commShiftIso (1 : ℤ)).hom.app _ ≫ e.hom.left⟦(1 : ℤ)⟧', _, ?_, H⟩
  refine Triangle.isoMk _ _ (Arrow.leftFunc.mapIso e.symm) (Arrow.rightFunc.mapIso e.symm)
    (Iso.refl _) e.inv.w.symm (by simp) ?_
  dsimp
  simp only [assoc, id_comp, ← Functor.map_comp, ← Arrow.comp_left, e.hom_inv_id, Arrow.id_left,
    Functor.mapArrow_obj, Arrow.mk_left, Functor.map_id, comp_id]

variable [W.IsCompatibleWithTriangulation]

set_option backward.isDefEq.respectTransparency false in

include W in

lemma complete_distinguished_triangle_morphism (T₁ T₂ : Triangle D)
    (hT₁ : T₁ ∈ L.essImageDistTriang) (hT₂ : T₂ ∈ L.essImageDistTriang)
    (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂) (fac : T₁.mor₁ ≫ b = a ≫ T₂.mor₁) :
    ∃ c, T₁.mor₂ ≫ c = b ≫ T₂.mor₂ ∧ T₁.mor₃ ≫ a⟦1⟧' = c ≫ T₂.mor₃ := by
  refine L.complete_distinguished_essImageDistTriang_morphism ?_ T₁ T₂ hT₁ hT₂ a b fac
  clear a b fac hT₁ hT₂ T₁ T₂
  intro T₁ T₂ hT₁ hT₂ a b fac
  obtain ⟨α, hα⟩ := exists_leftFraction L W a
  obtain ⟨β, hβ⟩ := (MorphismProperty.RightFraction.mk α.s α.hs T₂.mor₁).exists_leftFraction
  obtain ⟨γ, hγ⟩ := exists_leftFraction L W (b ≫ L.map β.s)
  have := inverts L W β.s β.hs
  have := inverts L W γ.s γ.hs
  dsimp at hβ
  obtain ⟨Z₂, σ, hσ, fac⟩ := (MorphismProperty.map_eq_iff_postcomp L W
    (α.f ≫ β.f ≫ γ.s) (T₁.mor₁ ≫ γ.f)).1 (by
      rw [← cancel_mono (L.map β.s), assoc, assoc, hγ, ← cancel_mono (L.map γ.s),
        assoc, assoc, assoc, hα, MorphismProperty.LeftFraction.map_comp_map_s,
        ← Functor.map_comp] at fac
      rw [fac, ← Functor.map_comp_assoc, hβ, Functor.map_comp, Functor.map_comp,
        Functor.map_comp, assoc, MorphismProperty.LeftFraction.map_comp_map_s_assoc])
  simp only [assoc] at fac
  obtain ⟨Y₃, g, h, hT₃⟩ := Pretriangulated.distinguished_cocone_triangle (β.f ≫ γ.s ≫ σ)
  let T₃ := Triangle.mk (β.f ≫ γ.s ≫ σ) g h
  change T₃ ∈ distTriang C at hT₃
  have hβγσ : W (β.s ≫ γ.s ≫ σ) := W.comp_mem _ _ β.hs (W.comp_mem _ _ γ.hs hσ)
  obtain ⟨ψ₃, hψ₃, hψ₁, hψ₂⟩ := MorphismProperty.compatible_with_triangulation
    T₂ T₃ hT₂ hT₃ α.s (β.s ≫ γ.s ≫ σ) α.hs hβγσ (by dsimp [T₃]; rw [reassoc_of% hβ])
  let ψ : T₂ ⟶ T₃ := Triangle.homMk _ _ α.s (β.s ≫ γ.s ≫ σ) ψ₃
    (by dsimp [T₃]; rw [reassoc_of% hβ]) hψ₁ hψ₂
  have : IsIso (L.mapTriangle.map ψ) := Triangle.isIso_of_isIsos _
    (inverts L W α.s α.hs) (inverts L W _ hβγσ) (inverts L W ψ₃ hψ₃)
  refine ⟨L.mapTriangle.map (completeDistinguishedTriangleMorphism T₁ T₃ hT₁ hT₃ α.f
      (γ.f ≫ σ) fac.symm) ≫ inv (L.mapTriangle.map ψ), ?_, ?_⟩
  · rw [← cancel_mono (L.mapTriangle.map ψ).hom₁, ← comp_hom₁, assoc, IsIso.inv_hom_id, comp_id]
    dsimp [ψ]
    rw [hα, MorphismProperty.LeftFraction.map_comp_map_s]
  · rw [← cancel_mono (L.mapTriangle.map ψ).hom₂, ← comp_hom₂, assoc, IsIso.inv_hom_id, comp_id]
    dsimp [ψ]
    simp only [Functor.map_comp, reassoc_of% hγ,
      MorphismProperty.LeftFraction.map_comp_map_s_assoc]

variable [HasZeroObject D] [Preadditive D] [∀ (n : ℤ), (shiftFunctor D n).Additive] [L.Additive]
