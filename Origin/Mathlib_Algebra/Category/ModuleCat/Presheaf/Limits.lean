/-
Extracted from Algebra/Category/ModuleCat/Presheaf/Limits.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-! # Limits in categories of presheaves of modules

In this file, it is shown that under suitable assumptions,
limits exist in the category `PresheafOfModules R`.

-/

universe v v₁ v₂ u₁ u₂ u u'

open CategoryTheory Category Limits

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}
  {J : Type u₂} [Category.{v₂} J]
  (F : J ⥤ PresheafOfModules.{v} R)

section Limits

variable [∀ X, Small.{v} ((F ⋙ evaluation R X) ⋙ forget _).sections]

set_option backward.isDefEq.respectTransparency false in

def evaluationJointlyReflectsLimits (c : Cone F)
    (hc : ∀ (X : Cᵒᵖ), IsLimit ((evaluation R X).mapCone c)) : IsLimit c where
  lift s :=
    { app := fun X => (hc X).lift ((evaluation R X).mapCone s)
      naturality := fun {X Y} f ↦ by
        apply (isLimitOfPreserves (ModuleCat.restrictScalars (R.map f).hom) (hc Y)).hom_ext
        intro j
        have h₁ := (c.π.app j).naturality f
        have h₂ := (hc X).fac ((evaluation R X).mapCone s) j
        rw [Functor.mapCone_π_app, assoc, assoc, ← Functor.map_comp, IsLimit.fac]
        dsimp at h₁ h₂ ⊢
        rw [h₁, reassoc_of% h₂, Hom.naturality] }
  fac s j := by
    ext1 X
    exact (hc X).fac ((evaluation R X).mapCone s) j
  uniq s m hm := by
    ext1 X
    apply (hc X).uniq ((evaluation R X).mapCone s)
    intro j
    dsimp
    rw [← hm, comp_app]

-- INSTANCE (free from Core): {X

set_option backward.isDefEq.respectTransparency false in
