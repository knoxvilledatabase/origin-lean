/-
Extracted from CategoryTheory/Adjunction/Lifting/Right.lean
Genuine: 3 of 4 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Adjoint lifting

This file gives two constructions for building right adjoints: the adjoint triangle theorem and the
adjoint lifting theorem.

The adjoint triangle theorem concerns a functor `F : B ⥤ A` with a right adjoint `U` such
that `η_X : X ⟶ UFX` is a regular mono. Then for any category `C` with equalizers of coreflexive
pairs, a functor `L : C ⥤ B` has a right adjoint if (and only if) the composite `L ⋙ F` does.
Note that the condition on `F` regarding `η_X` is automatically satisfied in the case when `F` is
a comonadic functor, giving the corollary: `isLeftAdjoint_triangle_lift_comonadic`, i.e. if `F` is
comonadic, `C` has coreflexive equalizers then `L : C ⥤ B` has a right adjoint provided `L ⋙ F`
does.

The adjoint lifting theorem says that given a commutative square of functors (up to isomorphism):

```
      Q
    A → B
  U ↓   ↓ V
    C → D
      L
```

where `V` is comonadic, `U` has a right adjoint, and `A` has coreflexive equalizers, then if `L` has
a right adjoint then `Q` has a right adjoint.

## Implementation

It is more convenient to prove this theorem by assuming we are given the explicit adjunction rather
than just a functor known to be a right adjoint. In docstrings, we write `(η, ε)` for the unit
and counit of the adjunction `adj₁ : F ⊣ U` and `(ι, δ)` for the unit and counit of the adjunction
`adj₂ : L ⋙ F ⊣ U'`.

This file has been adapted from `Mathlib/CategoryTheory/Adjunction/Lifting/Left.lean`.
Please try to keep them in sync.

## TODO

- Dualise to lift left adjoints through comonads (by reversing 2-cells).
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

namespace LiftRightAdjoint

variable {U : A ⥤ B} {F : B ⥤ A} (L : C ⥤ B) (U' : A ⥤ C)

variable (adj₁ : F ⊣ U) (adj₂ : L ⋙ F ⊣ U')

set_option backward.isDefEq.respectTransparency false in

def unitEqualises (h : ∀ X : B, RegularMono (adj₁.unit.app X)) (X : B) :
    IsLimit (Fork.ofι (adj₁.unit.app X) (adj₁.unit_naturality _)) :=
  Fork.IsLimit.mk' _ fun s => by
    have := fun Y ↦ h Y |>.mono
    refine ⟨((h X).lift' s.ι ?_).1, ?_, ?_⟩
    · rw [← cancel_mono (adj₁.unit.app ((h X).Z)), assoc, ← adj₁.unit_naturality (h _).left]
      dsimp only [Functor.comp_obj]
      have := s.condition
      dsimp only [Functor.comp_obj] at this
      rw [← assoc, ← this, assoc, ← U.map_comp, ← F.map_comp, RegularMono.w, F.map_comp,
        U.map_comp, s.condition_assoc, assoc, ← adj₁.unit_naturality (h _).right]
    · apply ((h X).lift' s.ι _).2
    · intro m hm
      rw [← cancel_mono (adj₁.unit.app X)]
      apply hm.trans ((h X).lift' s.ι _).2.symm

def otherMap (X : B) : U'.obj (F.obj X) ⟶ U'.obj (F.obj (U.obj (F.obj X))) :=
  adj₂.unit.app _ ≫ U'.map (F.map (adj₁.unit.app _ ≫ (U.map (adj₂.counit.app _))))

set_option backward.isDefEq.respectTransparency false in

-- INSTANCE (free from Core): (X

variable [HasCoreflexiveEqualizers C]

noncomputable def constructRightAdjointObj (Y : B) : C :=
  equalizer (U'.map (F.map (adj₁.unit.app Y))) (otherMap _ _ adj₁ adj₂ Y)

set_option backward.isDefEq.respectTransparency false in
