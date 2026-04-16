/-
Extracted from CategoryTheory/Adjunction/Lifting/Left.lean
Genuine: 9 | Conflates: 0 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core
import Mathlib.CategoryTheory.Monad.Adjunction
import Mathlib.CategoryTheory.Monad.Coequalizer

noncomputable section

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

This file has been adapted to `Mathlib.CategoryTheory.Adjunction.Lifting.Right`.
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

def counitCoequalises [∀ X : B, RegularEpi (adj₁.counit.app X)] (X : B) :
    IsColimit (Cofork.ofπ (adj₁.counit.app X) (adj₁.counit_naturality _)) :=
  Cofork.IsColimit.mk' _ fun s => by
    refine ⟨(RegularEpi.desc' (adj₁.counit.app X) s.π ?_).1, ?_, ?_⟩
    · rw [← cancel_epi (adj₁.counit.app (RegularEpi.W (adj₁.counit.app X)))]
      rw [← adj₁.counit_naturality_assoc RegularEpi.left]
      dsimp only [Functor.comp_obj]
      rw [← s.condition, ← F.map_comp_assoc, ← U.map_comp, RegularEpi.w, U.map_comp,
        F.map_comp_assoc, s.condition, ← adj₁.counit_naturality_assoc RegularEpi.right]
    · apply (RegularEpi.desc' (adj₁.counit.app X) s.π _).2
    · intro m hm
      rw [← cancel_epi (adj₁.counit.app X)]
      apply hm.trans (RegularEpi.desc' (adj₁.counit.app X) s.π _).2.symm

def otherMap (X) : F'.obj (U.obj (F.obj (U.obj X))) ⟶ F'.obj (U.obj X) :=
  F'.map (U.map (F.map (adj₂.unit.app _) ≫ adj₁.counit.app _)) ≫ adj₂.counit.app _

instance (X : B) :
    IsReflexivePair (F'.map (U.map (adj₁.counit.app X))) (otherMap _ _ adj₁ adj₂ X) :=
  IsReflexivePair.mk' (F'.map (adj₁.unit.app (U.obj X)))
    (by
      rw [← F'.map_comp, adj₁.right_triangle_components]
      apply F'.map_id)
    (by
      dsimp [otherMap]
      rw [← F'.map_comp_assoc, U.map_comp, adj₁.unit_naturality_assoc,
        adj₁.right_triangle_components, comp_id, adj₂.left_triangle_components])

variable [HasReflexiveCoequalizers A]

noncomputable def constructLeftAdjointObj (Y : B) : A :=
  coequalizer (F'.map (U.map (adj₁.counit.app Y))) (otherMap _ _ adj₁ adj₂ Y)

set_option linter.unusedVariables false in
/-- The homset equivalence which helps show that `R` is a right adjoint. -/

@[simps!] -- Porting note: Originally `@[simps (config := { rhsMd := semireducible })]`
noncomputable def constructLeftAdjointEquiv [∀ X : B, RegularEpi (adj₁.counit.app X)] (Y : A)
    (X : B) : (constructLeftAdjointObj _ _ adj₁ adj₂ X ⟶ Y) ≃ (X ⟶ R.obj Y) :=
  calc
    (constructLeftAdjointObj _ _ adj₁ adj₂ X ⟶ Y) ≃
        { f : F'.obj (U.obj X) ⟶ Y //
          F'.map (U.map (adj₁.counit.app X)) ≫ f = otherMap _ _ adj₁ adj₂ _ ≫ f } :=
      Cofork.IsColimit.homIso (colimit.isColimit _) _
    _ ≃ { g : U.obj X ⟶ U.obj (R.obj Y) //
          U.map (F.map g ≫ adj₁.counit.app _) = U.map (adj₁.counit.app _) ≫ g } := by
      apply (adj₂.homEquiv _ _).subtypeEquiv _
      intro f
      rw [← (adj₂.homEquiv _ _).injective.eq_iff, eq_comm, adj₂.homEquiv_naturality_left,
        otherMap, assoc, adj₂.homEquiv_naturality_left, ← adj₂.counit_naturality,
        adj₂.homEquiv_naturality_left, adj₂.homEquiv_unit, adj₂.right_triangle_components,
        comp_id, Functor.comp_map, ← U.map_comp, assoc, ← adj₁.counit_naturality,
        adj₂.homEquiv_unit, adj₂.homEquiv_unit, F.map_comp, assoc]
      rfl
    _ ≃ { z : F.obj (U.obj X) ⟶ R.obj Y // _ } := by
      apply (adj₁.homEquiv _ _).symm.subtypeEquiv
      intro g
      rw [← (adj₁.homEquiv _ _).symm.injective.eq_iff, adj₁.homEquiv_counit,
        adj₁.homEquiv_counit, adj₁.homEquiv_counit, F.map_comp, assoc, U.map_comp, F.map_comp,
        assoc, adj₁.counit_naturality, adj₁.counit_naturality_assoc]
      apply eq_comm
    _ ≃ (X ⟶ R.obj Y) := (Cofork.IsColimit.homIso (counitCoequalises adj₁ X) _).symm

attribute [local simp] Adjunction.homEquiv_counit

noncomputable def constructLeftAdjoint [∀ X : B, RegularEpi (adj₁.counit.app X)] : B ⥤ A := by
  refine Adjunction.leftAdjointOfEquiv (fun X Y => constructLeftAdjointEquiv R _ adj₁ adj₂ Y X) ?_
  intro X Y Y' g h
  rw [constructLeftAdjointEquiv_apply, constructLeftAdjointEquiv_apply,
    Equiv.symm_apply_eq, Subtype.ext_iff]
  dsimp
  -- This used to be `rw`, but we need `erw` after https://github.com/leanprover/lean4/pull/2644
  erw [Cofork.IsColimit.homIso_natural, Cofork.IsColimit.homIso_natural]
  erw [adj₂.homEquiv_naturality_right]
  simp_rw [Functor.comp_map]
  -- This used to be `simp`, but we need `aesop_cat` after https://github.com/leanprover/lean4/pull/2644
  aesop_cat

end LiftLeftAdjoint

lemma isRightAdjoint_triangle_lift {U : B ⥤ C} {F : C ⥤ B} (R : A ⥤ B) (adj₁ : F ⊣ U)
    [∀ X : B, RegularEpi (adj₁.counit.app X)] [HasReflexiveCoequalizers A]
    [(R ⋙ U).IsRightAdjoint ] : R.IsRightAdjoint where
  exists_leftAdjoint :=
    ⟨LiftLeftAdjoint.constructLeftAdjoint R _ adj₁ (Adjunction.ofIsRightAdjoint _),
      ⟨Adjunction.adjunctionOfEquivLeft _ _⟩⟩

lemma isRightAdjoint_triangle_lift_monadic (U : B ⥤ C) [MonadicRightAdjoint U] {R : A ⥤ B}
    [HasReflexiveCoequalizers A] [(R ⋙ U).IsRightAdjoint] : R.IsRightAdjoint := by
  let R' : A ⥤ _ := R ⋙ Monad.comparison (monadicAdjunction U)
  rsuffices : R'.IsRightAdjoint
  · let this : (R' ⋙ (Monad.comparison (monadicAdjunction U)).inv).IsRightAdjoint := by
      infer_instance
    refine ((Adjunction.ofIsRightAdjoint
      (R' ⋙ (Monad.comparison (monadicAdjunction U)).inv)).ofNatIsoRight ?_).isRightAdjoint
    exact isoWhiskerLeft R (Monad.comparison _).asEquivalence.unitIso.symm ≪≫ R.rightUnitor
  let this : (R' ⋙ Monad.forget (monadicAdjunction U).toMonad).IsRightAdjoint := by
    refine ((Adjunction.ofIsRightAdjoint (R ⋙ U)).ofNatIsoRight ?_).isRightAdjoint
    exact isoWhiskerLeft R (Monad.comparisonForget (monadicAdjunction U)).symm
  let this : ∀ X, RegularEpi ((Monad.adj (monadicAdjunction U).toMonad).counit.app X) := by
    intro X
    simp only [Monad.adj_counit]
    exact ⟨_, _, _, _, Monad.beckAlgebraCoequalizer X⟩
  exact isRightAdjoint_triangle_lift R' (Monad.adj _)

variable {D : Type u₄}

variable [Category.{v₄} D]

lemma isRightAdjoint_square_lift (Q : A ⥤ B) (V : B ⥤ D) (U : A ⥤ C) (R : C ⥤ D)
    (comm : U ⋙ R ≅ Q ⋙ V) [U.IsRightAdjoint] [V.IsRightAdjoint] [R.IsRightAdjoint]
    [∀ X, RegularEpi ((Adjunction.ofIsRightAdjoint V).counit.app X)] [HasReflexiveCoequalizers A] :
    Q.IsRightAdjoint :=
  have := ((Adjunction.ofIsRightAdjoint (U ⋙ R)).ofNatIsoRight comm).isRightAdjoint
  isRightAdjoint_triangle_lift Q (Adjunction.ofIsRightAdjoint V)

lemma isRightAdjoint_square_lift_monadic (Q : A ⥤ B) (V : B ⥤ D) (U : A ⥤ C) (R : C ⥤ D)
    (comm : U ⋙ R ≅ Q ⋙ V) [U.IsRightAdjoint] [MonadicRightAdjoint V] [R.IsRightAdjoint]
    [HasReflexiveCoequalizers A] : Q.IsRightAdjoint :=
  have := ((Adjunction.ofIsRightAdjoint (U ⋙ R)).ofNatIsoRight comm).isRightAdjoint
  isRightAdjoint_triangle_lift_monadic V

end CategoryTheory
