/-
Extracted from AlgebraicGeometry/RelativeGluing.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Relative gluing

In this file we show a relative gluing lemma (see https://stacks.math.columbia.edu/tag/01LH):
If `{Uᵢ}` is a locally directed open cover of `S` and we have a compatible family of `Xᵢ` over `Uᵢ`,
the `Xᵢ` glue to a morphism `f : X ⟶ S` such that `Xᵢ ≅ f⁻¹ Uᵢ`.
-/

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in

lemma Scheme.isLocallyDirected_of_equifibered_of_injective {J : Type*} [Category J]
    {F G : J ⥤ Scheme.{u}} (s : F ⟶ G) [Quiver.IsThin J] (hs : s.Equifibered)
    (H : ∀ {i j} (hij : i ⟶ j), Function.Injective (F.map hij))
    [(G ⋙ Scheme.forget).IsLocallyDirected] :
    (F ⋙ Scheme.forget).IsLocallyDirected where
  cond {i j k} fi fj xi xj heq := by
    simp only [Functor.comp_obj, Scheme.forget_obj, Functor.comp_map, Scheme.forget_map] at heq
    obtain ⟨l, fli, flj, x, hi, hj⟩ := (G ⋙ Scheme.forget).exists_map_eq_of_isLocallyDirected fi fj
        (s.app i xi) (s.app j xj) <| by
      simp only [Functor.comp_obj, forget_obj, Functor.comp_map, forget_map,
        ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk]
      dsimp at heq
      rw [← Scheme.Hom.comp_apply, ← s.naturality, Scheme.Hom.comp_apply, heq,
        ← Scheme.Hom.comp_apply, s.naturality]
      simp
    use l, fli, flj
    let e := (hs fli).isoPullback
    obtain ⟨z, h1, h2⟩ := Scheme.Pullback.exists_preimage_pullback xi x hi.symm
    refine ⟨e.inv z, ?_, ?_⟩
    · simp [← h1, ← Scheme.Hom.comp_apply, e]
    · apply H fj
      simp only [Functor.comp_obj, forget_obj, Functor.comp_map, forget_map,
        ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk, ← Scheme.Hom.comp_apply,
        Category.assoc, ← Functor.map_comp, show flj ≫ fj = fli ≫ fi by subsingleton]
      dsimp at heq
      simp [e, Functor.map_comp, ← heq, h1]

namespace Scheme.Cover

variable {S : Scheme.{u}} (𝒰 : S.OpenCover) [Category 𝒰.I₀] [𝒰.LocallyDirected]
