/-
Extracted from Algebra/Homology/BifunctorHomotopy.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The action of a bifunctor on homological complexes factors through homotopies

Given a `TotalComplexShape c₁ c₂ c`, a functor `F : C₁ ⥤ C₂ ⥤ D`,
we show in this file that up to homotopy the morphism
`mapBifunctorMap f₁ f₂ F c` only depends on the homotopy classes of
the morphism `f₁` in `HomologicalComplex C c₁` and of
the morphism `f₂` in `HomologicalComplex C c₂`.

-/

assert_not_exists TwoSidedIdeal

open CategoryTheory Category Limits

variable {C₁ C₂ D I₁ I₂ J : Type*} [Category* C₁] [Category* C₂] [Category* D]
  [Preadditive C₁] [Preadditive C₂] [Preadditive D]
  {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}

namespace HomologicalComplex

variable {K₁ L₁ : HomologicalComplex C₁ c₁} {f₁ f₁' : K₁ ⟶ L₁} (h₁ : Homotopy f₁ f₁')
  {K₂ L₂ : HomologicalComplex C₂ c₂} (f₂ f₂' : K₂ ⟶ L₂) (h₂ : Homotopy f₂ f₂')
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive] [∀ X₁, (F.obj X₁).Additive]
  (c : ComplexShape J) [DecidableEq J] [TotalComplexShape c₁ c₂ c]
  [HasMapBifunctor K₁ K₂ F c] [HasMapBifunctor L₁ L₂ F c]

namespace mapBifunctorMapHomotopy

noncomputable def hom₁ (j j' : J) :
    (mapBifunctor K₁ K₂ F c).X j ⟶ (mapBifunctor L₁ L₂ F c).X j' :=
  HomologicalComplex₂.totalDesc _
    (fun i₁ i₂ _ => ComplexShape.ε₁ c₁ c₂ c (c₁.prev i₁, i₂) •
      (F.map (h₁.hom i₁ (c₁.prev i₁))).app (K₂.X i₂) ≫
      (F.obj (L₁.X (c₁.prev i₁))).map (f₂.f i₂) ≫ ιMapBifunctorOrZero L₁ L₂ F c _ _ j')

set_option backward.isDefEq.respectTransparency false in
