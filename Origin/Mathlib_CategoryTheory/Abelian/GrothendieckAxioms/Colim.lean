/-
Extracted from CategoryTheory/Abelian/GrothendieckAxioms/Colim.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Exactness of colimits

In this file, we shall study exactness properties of colimits.
First, we translate the assumption that `colim : (J ⥤ C) ⥤ C`
preserves monomorphisms (resp. preserves epimorphisms, resp. is exact)
into statements involving arbitrary cocones instead of the ones
given by the colimit API. We also show that when an inductive system
involves only monomorphisms, then the "inclusion" morphism
into the colimit is also a monomorphism (assuming `J`
is filtered and `C` satisfies AB5).

-/

universe v' v u' u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : Type u'} [Category.{v'} J]

namespace Limits

set_option backward.isDefEq.respectTransparency false in

lemma colim.map_mono' [HasColimitsOfShape J C]
    [(colim : (J ⥤ C) ⥤ C).PreservesMonomorphisms]
    {X₁ X₂ : J ⥤ C} (φ : X₁ ⟶ X₂) [Mono φ]
    {c₁ : Cocone X₁} (hc₁ : IsColimit c₁) {c₂ : Cocone X₂} (hc₂ : IsColimit c₂)
    (f : c₁.pt ⟶ c₂.pt) (hf : ∀ j, c₁.ι.app j ≫ f = φ.app j ≫ c₂.ι.app j) : Mono f := by
  refine ((MorphismProperty.monomorphisms C).arrow_mk_iso_iff ?_).2
    ((inferInstance : Mono (colim.map φ)))
  exact Arrow.isoMk
    (IsColimit.coconePointUniqueUpToIso hc₁ (colimit.isColimit _))
    (IsColimit.coconePointUniqueUpToIso hc₂ (colimit.isColimit _))
    (hc₁.hom_ext (fun j ↦ by
      dsimp
      rw [IsColimit.comp_coconePointUniqueUpToIso_hom_assoc,
        colimit.cocone_ι, ι_colimMap, reassoc_of% (hf j),
        IsColimit.comp_coconePointUniqueUpToIso_hom, colimit.cocone_ι]))

set_option backward.isDefEq.respectTransparency false in

lemma colim.map_epi'
    {X₁ X₂ : J ⥤ C} (φ : X₁ ⟶ X₂) [∀ j, Epi (φ.app j)]
    (c₁ : Cocone X₁) {c₂ : Cocone X₂} (hc₂ : IsColimit c₂)
    (f : c₁.pt ⟶ c₂.pt) (hf : ∀ j, c₁.ι.app j ≫ f = φ.app j ≫ c₂.ι.app j) : Epi f where
  left_cancellation {Z} g₁ g₂ h := hc₂.hom_ext (fun j ↦ by
    rw [← cancel_epi (φ.app j), ← reassoc_of% hf, h, reassoc_of% hf])

attribute [local instance] IsFiltered.isConnected

set_option backward.isDefEq.respectTransparency false in

lemma IsColimit.mono_ι_app_of_isFiltered
    {X : J ⥤ C} [∀ (j j' : J) (φ : j ⟶ j'), Mono (X.map φ)]
    {c : Cocone X} (hc : IsColimit c) [IsFiltered J] (j₀ : J)
    [HasColimitsOfShape (Under j₀) C]
    [(colim : (Under j₀ ⥤ C) ⥤ C).PreservesMonomorphisms] :
    Mono (c.ι.app j₀) := by
  let f : (Functor.const _).obj (X.obj j₀) ⟶ Under.forget j₀ ⋙ X :=
    { app j := X.map j.hom
      naturality _ _ g := by
        dsimp
        simp only [Category.id_comp, ← X.map_comp, Under.w] }
  have := NatTrans.mono_of_mono_app f
  exact colim.map_mono' f (isColimitConstCocone _ _)
    ((Functor.Final.isColimitWhiskerEquiv _ _).symm hc) (c.ι.app j₀) (by cat_disch)

variable [HasColimitsOfShape J C] [HasExactColimitsOfShape J C] [HasZeroMorphisms C]
  (S : ShortComplex (J ⥤ C)) (hS : S.Exact)
  {c₁ : Cocone S.X₁} (hc₁ : IsColimit c₁) (c₂ : Cocone S.X₂) (hc₂ : IsColimit c₂)
  (c₃ : Cocone S.X₃) (hc₃ : IsColimit c₃)
  (f : c₁.pt ⟶ c₂.pt) (g : c₂.pt ⟶ c₃.pt)
  (hf : ∀ j, c₁.ι.app j ≫ f = S.f.app j ≫ c₂.ι.app j)
  (hg : ∀ j, c₂.ι.app j ≫ g = S.g.app j ≫ c₃.ι.app j)

set_option backward.isDefEq.respectTransparency false in
