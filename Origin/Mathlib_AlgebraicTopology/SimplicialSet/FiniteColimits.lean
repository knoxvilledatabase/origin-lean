/-
Extracted from AlgebraicTopology/SimplicialSet/FiniteColimits.lean
Genuine: 5 of 8 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Finite colimits of finite simplicial sets are finite

-/

universe u v

open CategoryTheory Limits

namespace SSet

variable {J : Type*} [Category J] [HasColimitsOfShape J (Type u)]
  {F : J ⥤ SSet.{u}} {c : Cocone F} (hc : IsColimit c)

include hc

lemma iSup_range_eq_top_of_isColimit :
    ⨆ (j : J), Subcomplex.range (c.ι.app j) = ⊤ := by
  ext n x
  simp only [Subfunctor.iSup_obj, Subfunctor.range_obj, Set.mem_iUnion, Set.mem_range,
    Subfunctor.top_obj, Set.top_eq_univ, Set.mem_univ, iff_true]
  exact Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves ((evaluation _ _).obj n) hc) x

set_option backward.isDefEq.respectTransparency false in

lemma range_eq_iSup_of_isColimit {X : SSet.{u}} (φ : c.pt ⟶ X) :
    Subcomplex.range φ = ⨆ (j : J), Subcomplex.range (c.ι.app j ≫ φ) := by
  conv_lhs => rw [← Category.id_comp φ]
  simp_rw [Subcomplex.range_comp, Subcomplex.range_eq_top, ← iSup_range_eq_top_of_isColimit hc,
    Subcomplex.image_iSup]

set_option backward.isDefEq.respectTransparency false in

lemma hasDimensionLT_of_isColimit {n : ℕ}
    (h : ∀ (j : J), HasDimensionLT (F.obj j) n) : HasDimensionLT c.pt n := by
  rw [← hasDimensionLT_subcomplex_top_iff, ← iSup_range_eq_top_of_isColimit hc,
    hasDimensionLT_iSup_iff]
  infer_instance

set_option backward.isDefEq.respectTransparency false in

lemma finite_of_isColimit [Finite J] (h : ∀ (j : J), (F.obj j).Finite) :
    c.pt.Finite := by
  rw [← finite_subcomplex_top_iff, ← iSup_range_eq_top_of_isColimit hc, finite_iSup_iff]
  infer_instance

end

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): (X

-- INSTANCE (free from Core): {ι

set_option backward.isDefEq.respectTransparency false in

lemma range_eq_iSup_sigma_ι
    {ι : Type v} [HasColimitsOfShape (Discrete ι) (Type u)]
    {X : ι → SSet.{u}} {Y : SSet.{u}} [HasCoproduct X]
    (f : ∐ X ⟶ Y) :
    Subcomplex.range f = ⨆ (i : ι), Subcomplex.range (Sigma.ι X i ≫ f) := by
  rw [range_eq_iSup_of_isColimit (coproductIsCoproduct X) f]
  refine le_antisymm ?_ ?_
  · simp only [iSup_le_iff, Discrete.forall]
    intro i
    exact le_trans (by rfl) (le_iSup _ i)
  · simp only [iSup_le_iff]
    intro i
    exact le_trans (by rfl) (le_iSup _ ⟨i⟩)

end SSet
