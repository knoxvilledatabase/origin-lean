/-
Extracted from CategoryTheory/Monoidal/Action/LinearFunctor.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! # Functors that are linear with respect to an action

Given a monoidal category `C` acting on the left or on the right on categories
`D` and `D'`, we introduce the following typeclasses on functors `F : D ⥤ D'` to
express compatibility of `F` with the action of `C`:
* `F.LaxLeftLinear C` bundles the "lineator" as a morphism
  `μₗ : c ⊙ₗ F.obj d ⟶ F.obj (c ⊙ₗ d)`.
* `F.LaxRightLinear C` bundles the "lineator" as a morphism
  `μᵣ : F.obj d ⊙ᵣ c ⟶ F.obj (d ⊙ᵣ c)`.
* `F.OplaxLeftLinear C` bundles the "lineator" as a morphism
  `δₗ : F.obj (c ⊙ₗ d) ⟶ c ⊙ₗ F.obj d`.
* `F.OplaxRightLinear C` bundles the "lineator" as a morphism
  `δᵣ : F.obj (d ⊙ᵣ c) ⟶ F.obj d ⊙ᵣ c`.
* `F.LeftLinear C` expresses that `F` has both a `LaxLeftLinear C` and
  an `F.OplaxLeftLinear C` structure, and that they are compatible, i.e.
  `δₗ F` is a left and right inverse to `μₗ`.
* `F.RightLinear C` expresses that `F` has both a `LaxRightLinear C` and
  an `F.OplaxRightLinear C` structure, and that they are compatible, i.e.
  `δᵣ F` is a left and right inverse to `μᵣ`.

-/

namespace CategoryTheory.Functor

variable {D D' : Type*} [Category* D] [Category* D']

open MonoidalCategory

section leftAction

open MonoidalLeftAction

class LaxLeftLinear
    (F : D ⥤ D') (C : Type*) [Category* C] [MonoidalCategory C]
    [MonoidalLeftAction C D] [MonoidalLeftAction C D'] where
  /-- The "μₗ" morphism. -/
  μₗ (F) (c : C) (d : D) : c ⊙ₗ F.obj d ⟶ F.obj (c ⊙ₗ d)
  μₗ_naturality_left (F) {c c' : C} (f : c ⟶ c') (d : D) :
    f ⊵ₗ F.obj d ≫ μₗ c' d = μₗ c d ≫ F.map (f ⊵ₗ d) := by cat_disch
  μₗ_naturality_right (F) (c : C) {d d' : D} (f : d ⟶ d') :
    c ⊴ₗ F.map f ≫ μₗ c d' = μₗ c d ≫ F.map (c ⊴ₗ f) := by cat_disch
  μₗ_associativity (F) (c c' : C) (d : D) :
    μₗ (c ⊗ c') d ≫ F.map (αₗ _ _ _).hom =
    (αₗ c c' (F.obj d)).hom ≫ c ⊴ₗ μₗ c' d ≫
      μₗ c (c' ⊙ₗ d) := by cat_disch
  μₗ_unitality (F) (d : D) :
    (λₗ (F.obj d)).hom = μₗ (𝟙_ C) d ≫ F.map (λₗ d).hom := by cat_disch

namespace LaxLeftLinear

attribute [reassoc (attr := simp)] μₗ_naturality_right

attribute [reassoc (attr := simp)] μₗ_naturality_left

attribute [reassoc (attr := simp)] μₗ_associativity

attribute [simp, reassoc] μₗ_unitality

variable
  (F : D ⥤ D') {C : Type*} [Category* C] [MonoidalCategory C]
  [MonoidalLeftAction C D] [MonoidalLeftAction C D']
  [F.LaxLeftLinear C]
