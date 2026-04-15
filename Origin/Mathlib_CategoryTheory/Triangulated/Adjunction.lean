/-
Extracted from CategoryTheory/Triangulated/Adjunction.lean
Genuine: 8 of 17 | Dissolved: 0 | Infrastructure: 9
-/
import Origin.Core

/-!
# The adjoint functor is triangulated

If a functor `F : C ⥤ D` between pretriangulated categories is triangulated, and if we
have an adjunction `F ⊣ G`, then `G` is also a triangulated functor. We deduce the
symmetric statement (if `G` is a triangulated functor, then so is `F`) using opposite
categories.

We then introduce a class `IsTriangulated` for adjunctions: an adjunction `F ⊣ G`
is called triangulated if both `F` and `G` are triangulated, and if the adjunction
is compatible with the shifts by `ℤ` on `F` and `G` (in the sense of `Adjunction.CommShift`);
we prove that this is compatible with composition and that the identity adjunction is
triangulated.
Thanks to the results above, an adjunction carrying an `Adjunction.CommShift` instance
is triangulated as soon as one of the adjoint functors is triangulated.

We finally specialize these structures to equivalences of categories, and prove that,
if `E : C ≌ D` is an equivalence of pretriangulated categories, then
`E.functor` is triangulated if and only if `E.inverse` is triangulated.

-/

assert_not_exists TwoSidedIdeal

namespace CategoryTheory

open Category Limits Preadditive Pretriangulated Adjunction

variable {C D : Type*} [Category* C] [Category* D] [HasZeroObject C] [HasZeroObject D]
  [Preadditive C] [Preadditive D] [HasShift C ℤ] [HasShift D ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]

namespace Adjunction

variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.CommShift ℤ] [G.CommShift ℤ]
  [adj.CommShift ℤ]

set_option backward.isDefEq.respectTransparency false in

include adj in

lemma isTriangulated_rightAdjoint [F.IsTriangulated] : G.IsTriangulated where
  map_distinguished T hT := by
    have : G.Additive := adj.right_adjoint_additive
    obtain ⟨Z, f, g, mem⟩ := distinguished_cocone_triangle (G.map T.mor₁)
    obtain ⟨h, ⟨h₁, h₂⟩⟩ := complete_distinguished_triangle_morphism _ _
      (F.map_distinguished _ mem) hT (adj.counit.app T.obj₁) (adj.counit.app T.obj₂) (by simp)
    dsimp at h h₁ h₂ ⊢
    have h₁' : f ≫ adj.unit.app Z ≫ G.map h = G.map T.mor₂ := by
      simpa [homEquiv_apply] using DFunLike.congr_arg (adj.homEquiv _ _) h₁
    have h₂' : g ≫ (G.commShiftIso (1 : ℤ)).inv.app T.obj₁ =
        adj.homEquiv _ _ h ≫ G.map T.mor₃ := by
      apply (adj.homEquiv _ _).symm.injective
      simp only [Functor.comp_obj, homEquiv_counit, Functor.id_obj, Functor.map_comp, assoc,
        homEquiv_unit, counit_naturality, counit_naturality_assoc, left_triangle_components_assoc,
        ← h₂, adj.shift_counit_app, Iso.hom_inv_id_app_assoc]
    rw [assoc] at h₂
    have : Mono (adj.homEquiv _ _ h) := by
      rw [mono_iff_cancel_zero]
      intro _ φ hφ
      obtain ⟨ψ, rfl⟩ := Triangle.coyoneda_exact₃ _ mem φ (by
        dsimp
        simp only [homEquiv_unit, Functor.comp_obj] at hφ
        rw [← cancel_mono ((G.commShiftIso (1 : ℤ)).inv.app T.obj₁), assoc, h₂', zero_comp,
          homEquiv_unit, assoc, reassoc_of% hφ, zero_comp])
      dsimp at ψ hφ ⊢
      obtain ⟨α, hα⟩ := T.coyoneda_exact₂ hT ((adj.homEquiv _ _).symm ψ)
        ((adj.homEquiv _ _).injective (by simpa [homEquiv_counit, homEquiv_unit, ← h₁'] using hφ))
      have eq := DFunLike.congr_arg (adj.homEquiv _ _) hα
      simp only [homEquiv_counit, homEquiv_unit, comp_id,
        Functor.map_comp, unit_naturality_assoc, right_triangle_components] at eq
      have eq' := comp_distTriang_mor_zero₁₂ _ mem
      dsimp at eq eq'
      rw [eq, assoc, assoc, eq', comp_zero, comp_zero]
    have := isIso_of_yoneda_map_bijective (adj.homEquiv _ _ h) (fun Y => by
      constructor
      · intro φ₁ φ₂ hφ
        rw [← cancel_mono (adj.homEquiv _ _ h)]
        exact hφ
      · intro φ
        obtain ⟨ψ, hψ⟩ := Triangle.coyoneda_exact₁ _ mem (φ ≫ G.map T.mor₃ ≫
          (G.commShiftIso (1 : ℤ)).hom.app T.obj₁) (by
            dsimp
            rw [assoc, assoc, ← G.commShiftIso_hom_naturality, ← G.map_comp_assoc,
              comp_distTriang_mor_zero₃₁ _ hT, G.map_zero, zero_comp, comp_zero])
        dsimp at ψ hψ
        obtain ⟨α, hα⟩ : ∃ α, α = φ - ψ ≫ adj.homEquiv _ _ h := ⟨_, rfl⟩
        have hα₀ : α ≫ G.map T.mor₃ = 0 := by
          rw [hα, sub_comp, ← cancel_mono ((Functor.commShiftIso G (1 : ℤ)).hom.app T.obj₁),
            assoc, sub_comp, assoc, assoc, hψ, zero_comp, sub_eq_zero,
            ← cancel_mono ((Functor.commShiftIso G (1 : ℤ)).inv.app T.obj₁), assoc,
            assoc, assoc, assoc, h₂', Iso.hom_inv_id_app, comp_id]
        suffices ∃ (β : Y ⟶ Z), β ≫ adj.homEquiv _ _ h = α by
          obtain ⟨β, hβ⟩ := this
          refine ⟨ψ + β, ?_⟩
          dsimp
          rw [add_comp, hβ, hα, add_sub_cancel]
        obtain ⟨β, hβ⟩ := T.coyoneda_exact₃ hT ((adj.homEquiv _ _).symm α)
          ((adj.homEquiv _ _).injective (by simpa [homEquiv_unit, homEquiv_counit] using hα₀))
        refine ⟨adj.homEquiv _ _ β ≫ f, ?_⟩
        simpa [homEquiv_unit, h₁'] using congr_arg (adj.homEquiv _ _).toFun hβ.symm)
    refine isomorphic_distinguished _ mem _ (Iso.symm ?_)
    refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (asIso (adj.homEquiv Z T.obj₃ h)) ?_ ?_ ?_
    · simp
    · apply (adj.homEquiv _ _).symm.injective
      dsimp
      simp only [homEquiv_unit, homEquiv_counit, Functor.map_comp, assoc,
        counit_naturality, left_triangle_components_assoc, h₁, id_comp]
    · dsimp
      rw [Functor.map_id, comp_id, homEquiv_unit, assoc, ← G.map_comp_assoc, ← h₂,
        Functor.map_comp, Functor.map_comp, assoc, unit_naturality_assoc, assoc,
        Functor.commShiftIso_hom_naturality, ← adj.shift_unit_app_assoc,
        ← Functor.map_comp, right_triangle_components, Functor.map_id, comp_id]

include adj in

open Pretriangulated.Opposite Functor in

lemma isTriangulated_leftAdjoint [G.IsTriangulated] : F.IsTriangulated := by
  have := isTriangulated_rightAdjoint adj.op
  exact F.isTriangulated_of_op

class IsTriangulated : Prop where
  commShift : adj.CommShift ℤ := by infer_instance
  leftAdjoint_isTriangulated : F.IsTriangulated := by infer_instance
  rightAdjoint_isTriangulated : G.IsTriangulated := by infer_instance

namespace IsTriangulated

attribute [instance] commShift leftAdjoint_isTriangulated rightAdjoint_isTriangulated

lemma mk' [F.IsTriangulated] : adj.IsTriangulated where
  rightAdjoint_isTriangulated := adj.isTriangulated_rightAdjoint

lemma mk'' [G.IsTriangulated] : adj.IsTriangulated where
  leftAdjoint_isTriangulated := adj.isTriangulated_leftAdjoint

-- INSTANCE (free from Core): id

variable {E : Type*} [Category* E] {F' : D ⥤ E} {G' : E ⥤ D} (adj' : F' ⊣ G') [HasZeroObject E]
  [Preadditive E] [HasShift E ℤ] [∀ (n : ℤ), (shiftFunctor E n).Additive] [Pretriangulated E]
  [F'.CommShift ℤ] [G'.CommShift ℤ] [adj'.CommShift ℤ]

-- INSTANCE (free from Core): comp

end IsTriangulated

end Adjunction

namespace Equivalence

variable (E : C ≌ D) [E.functor.CommShift ℤ] [E.inverse.CommShift ℤ] [E.CommShift ℤ]

abbrev IsTriangulated : Prop := E.toAdjunction.IsTriangulated

namespace IsTriangulated

-- INSTANCE (free from Core): [E.IsTriangulated]

-- INSTANCE (free from Core): [E.IsTriangulated]

-- INSTANCE (free from Core): [h

-- INSTANCE (free from Core): [h

lemma mk' (h : E.functor.IsTriangulated) : E.IsTriangulated where
  rightAdjoint_isTriangulated := E.toAdjunction.isTriangulated_rightAdjoint

lemma mk'' (h : E.inverse.IsTriangulated) : E.IsTriangulated where
  leftAdjoint_isTriangulated := (mk' E.symm h).rightAdjoint_isTriangulated

set_option backward.isDefEq.respectTransparency false in

-- INSTANCE (free from Core): refl

-- INSTANCE (free from Core): symm

variable {D' : Type*} [Category* D'] [HasZeroObject D'] [Preadditive D'] [HasShift D' ℤ]
  [∀ (n : ℤ), (shiftFunctor D' n).Additive] [Pretriangulated D'] {E' : D ≌ D'}
  [E'.functor.CommShift ℤ] [E'.inverse.CommShift ℤ] [E'.CommShift ℤ]

set_option backward.isDefEq.respectTransparency false in

-- INSTANCE (free from Core): trans

end IsTriangulated

end Equivalence

end CategoryTheory
