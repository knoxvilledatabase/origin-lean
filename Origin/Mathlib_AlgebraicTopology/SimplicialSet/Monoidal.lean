/-
Extracted from AlgebraicTopology/SimplicialSet/Monoidal.lean
Genuine: 1 | Conflates: 0 | Dissolved: 0 | Infrastructure: 10
-/
import Origin.Core
import Mathlib.AlgebraicTopology.SimplicialSet.Basic
import Mathlib.CategoryTheory.ChosenFiniteProducts.FunctorCategory
import Mathlib.CategoryTheory.Monoidal.Types.Basic

/-!
# The monoidal category structure on simplicial sets

This file defines an instance of chosen finite products
for the category `SSet`. It follows from the fact
the `SSet` if a category of functors to the category
of types and that the category of types have chosen
finite products. As a result, we obtain a monoidal
category structure on `SSet`.

-/

universe u

open Simplicial CategoryTheory MonoidalCategory

namespace SSet

noncomputable instance : ChosenFiniteProducts SSet.{u} :=
  (inferInstance : ChosenFiniteProducts (SimplexCategoryᵒᵖ ⥤ Type u))

@[simp]
lemma leftUnitor_hom_app_apply (K : SSet.{u}) {Δ : SimplexCategoryᵒᵖ} (x : (𝟙_ _ ⊗ K).obj Δ) :
    (λ_ K).hom.app Δ x = x.2 := rfl

@[simp]
lemma leftUnitor_inv_app_apply (K : SSet.{u}) {Δ : SimplexCategoryᵒᵖ} (x : K.obj Δ) :
    (λ_ K).inv.app Δ x = ⟨PUnit.unit, x⟩ := rfl

@[simp]
lemma rightUnitor_hom_app_apply (K : SSet.{u}) {Δ : SimplexCategoryᵒᵖ} (x : (K ⊗ 𝟙_ _).obj Δ) :
    (ρ_ K).hom.app Δ x = x.1 := rfl

@[simp]
lemma rightUnitor_inv_app_apply (K : SSet.{u}) {Δ : SimplexCategoryᵒᵖ} (x : K.obj Δ) :
    (ρ_ K).inv.app Δ x = ⟨x, PUnit.unit⟩ := rfl

@[simp]
lemma tensorHom_app_apply {K K' L L' : SSet.{u}} (f : K ⟶ K') (g : L ⟶ L')
    {Δ : SimplexCategoryᵒᵖ} (x : (K ⊗ L).obj Δ) :
    (f ⊗ g).app Δ x = ⟨f.app Δ x.1, g.app Δ x.2⟩ := rfl

@[simp]
lemma whiskerLeft_app_apply (K : SSet.{u}) {L L' : SSet.{u}} (g : L ⟶ L')
    {Δ : SimplexCategoryᵒᵖ} (x : (K ⊗ L).obj Δ) :
    (K ◁ g).app Δ x = ⟨x.1, g.app Δ x.2⟩ := rfl

@[simp]
lemma whiskerRight_app_apply {K K' : SSet.{u}} (f : K ⟶ K') (L : SSet.{u})
    {Δ : SimplexCategoryᵒᵖ} (x : (K ⊗ L).obj Δ) :
    (f ▷ L).app Δ x = ⟨f.app Δ x.1, x.2⟩ := rfl

@[simp]
lemma associator_hom_app_apply (K L M : SSet.{u}) {Δ : SimplexCategoryᵒᵖ}
    (x : ((K ⊗ L) ⊗ M).obj Δ) :
    (α_ K L M).hom.app Δ x = ⟨x.1.1, x.1.2, x.2⟩ := rfl

@[simp]
lemma associator_inv_app_apply (K L M : SSet.{u}) {Δ : SimplexCategoryᵒᵖ}
    (x : (K ⊗ L ⊗ M).obj Δ) :
    (α_ K L M).inv.app Δ x = ⟨⟨x.1, x.2.1⟩, x.2.2⟩ := rfl

def unitHomEquiv (K : SSet.{u}) : (𝟙_ _ ⟶ K) ≃ K _[0] where
  toFun φ := φ.app _ PUnit.unit
  invFun x :=
    { app := fun Δ _ => K.map (SimplexCategory.const Δ.unop [0] 0).op x
      naturality := fun Δ Δ' f => by
        ext ⟨⟩
        dsimp
        rw [← FunctorToTypes.map_comp_apply]
        rfl }
  left_inv φ := by
    ext Δ ⟨⟩
    dsimp
    rw [← FunctorToTypes.naturality]
    rfl
  right_inv x := by simp

end SSet
