/-
Extracted from CategoryTheory/Adjunction/Lifting/Left.lean
Genuine: 3 of 4 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Adjoint lifting

This file gives two constructions for building left adjoints: the adjoint triangle theorem and the
adjoint lifting theorem.

The adjoint triangle theorem concerns a functor `U : B ⥤ C` with a left adjoint `F` such
that `ε_X : FUX ⟶ X` is a regular epi. Then for any category `A` with coequalizers of reflexive
pairs, a functor `R : A ⥤ B` has a left adjoint if (and only if) the composite `R ⋙ U` does.
Note that the condition on `U` regarding `ε_X` is automatically satisfied in the case when `U` is
a monadic functor, giving the corollary: `isRightAdjoint_triangle_lift_monadic`, i.e. if `U` is
monadic, `A` has reflexive coequalizers then `R : A ⥤ B` has a left adjoint provided `R ⋙ U` does.

The adjoint lifting theorem says that given a commutative square of functors (up to isomorphism):

```
      Q
    A → B
  U ↓   ↓ V
    C → D
      R
```

where `V` is monadic, `U` has a left adjoint, and `A` has reflexive coequalizers, then if `R` has a
left adjoint then `Q` has a left adjoint.

## Implementation

It is more convenient to prove this theorem by assuming we are given the explicit adjunction rather
than just a functor known to be a right adjoint. In docstrings, we write `(η, ε)` for the unit
and counit of the adjunction `adj₁ : F ⊣ U` and `(ι, δ)` for the unit and counit of the adjunction
`adj₂ : F' ⊣ R ⋙ U`.

This file has been adapted to `Mathlib/CategoryTheory/Adjunction/Lifting/Right.lean`.
Please try to keep them in sync.

## TODO

- Dualise to lift right adjoints through monads (by reversing 2-cells).
- Investigate whether it is possible to give a more explicit description of the lifted adjoint,
  especially in the case when the isomorphism `comm` is `Iso.refl _`

## References
* https://ncatlab.org/nlab/show/adjoint+triangle+theorem
* https://ncatlab.org/nlab/show/adjoint+lifting+theorem
* Adjoint Lifting Theorems for Categories of Algebras (PT Johnstone, 1975)
* A unified approach to the lifting of adjoints (AJ Power, 1988)
-/

namespace CategoryTheory

open Category Limits

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {A : Type u₁} {B : Type u₂} {C : Type u₃}

variable [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]

namespace LiftLeftAdjoint

variable {U : B ⥤ C} {F : C ⥤ B} (R : A ⥤ B) (F' : C ⥤ A)

variable (adj₁ : F ⊣ U) (adj₂ : F' ⊣ R ⋙ U)

set_option backward.isDefEq.respectTransparency false in

def counitCoequalises (h : ∀ X : B, RegularEpi (adj₁.counit.app X)) (X : B) :
    IsColimit (Cofork.ofπ (adj₁.counit.app X) (adj₁.counit_naturality _)) :=
  Cofork.IsColimit.mk' _ fun s => by
    have := fun Y ↦ h Y |>.epi
    refine ⟨((h X).desc' s.π ?_).1, ?_, ?_⟩
    · rw [← cancel_epi (adj₁.counit.app (h X).W)]
      rw [← adj₁.counit_naturality_assoc (h X).left]
      dsimp
      rw [← dsimp% s.condition, ← F.map_comp_assoc, ← U.map_comp, RegularEpi.w, U.map_comp,
        F.map_comp_assoc, s.condition, ← adj₁.counit_naturality_assoc (h X).right]
    · apply ((h X).desc' s.π _).2
    · intro m hm
      rw [← cancel_epi (adj₁.counit.app X)]
      apply hm.trans ((h _).desc' s.π _).2.symm

def otherMap (X) : F'.obj (U.obj (F.obj (U.obj X))) ⟶ F'.obj (U.obj X) :=
  F'.map (U.map (F.map (adj₂.unit.app _) ≫ adj₁.counit.app _)) ≫ adj₂.counit.app _

set_option backward.isDefEq.respectTransparency false in

-- INSTANCE (free from Core): (X

variable [HasReflexiveCoequalizers A]

noncomputable def constructLeftAdjointObj (Y : B) : A :=
  coequalizer (F'.map (U.map (adj₁.counit.app Y))) (otherMap _ _ adj₁ adj₂ Y)

set_option backward.isDefEq.respectTransparency false in
