/-
Extracted from CategoryTheory/MorphismProperty/IsInvertedBy.lean
Genuine: 6 of 10 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# Morphism properties that are inverted by a functor

In this file, we introduce the predicate `P.IsInvertedBy F` which expresses
that the morphisms satisfying `P : MorphismProperty C` are mapped to
isomorphisms by a functor `F : C ⥤ D`.

This is used in the localization of categories API (folder `CategoryTheory.Localization`).

-/

universe w v v' u u'

namespace CategoryTheory

namespace MorphismProperty

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

def IsInvertedBy (P : MorphismProperty C) (F : C ⥤ D) : Prop :=
  ∀ ⦃X Y : C⦄ (f : X ⟶ Y) (_ : P f), IsIso (F.map f)

namespace IsInvertedBy

lemma of_le (P Q : MorphismProperty C) (F : C ⥤ D) (hQ : Q.IsInvertedBy F) (h : P ≤ Q) :
    P.IsInvertedBy F :=
  fun _ _ _ hf => hQ _ (h _ hf)

theorem of_comp {C₁ C₂ C₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
    (W : MorphismProperty C₁) (F : C₁ ⥤ C₂) (hF : W.IsInvertedBy F) (G : C₂ ⥤ C₃) :
    W.IsInvertedBy (F ⋙ G) := fun X Y f hf => by
  haveI := hF f hf
  dsimp
  infer_instance

set_option backward.isDefEq.respectTransparency false in

lemma prod {C₁ C₂ : Type*} [Category* C₁] [Category* C₂]
    {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}
    {E₁ E₂ : Type*} [Category* E₁] [Category* E₂] {F₁ : C₁ ⥤ E₁} {F₂ : C₂ ⥤ E₂}
    (h₁ : W₁.IsInvertedBy F₁) (h₂ : W₂.IsInvertedBy F₂) :
    (W₁.prod W₂).IsInvertedBy (F₁.prod F₂) := fun _ _ f hf => by
  rw [isIso_prod_iff]
  exact ⟨h₁ _ hf.1, h₂ _ hf.2⟩

lemma pi {J : Type w} {C : J → Type u} {D : J → Type u'}
    [∀ j, Category.{v} (C j)] [∀ j, Category.{v'} (D j)]
    (W : ∀ j, MorphismProperty (C j)) (F : ∀ j, C j ⥤ D j)
    (hF : ∀ j, (W j).IsInvertedBy (F j)) :
    (MorphismProperty.pi W).IsInvertedBy (Functor.pi F) := by
  intro _ _ f hf
  rw [isIso_pi_iff]
  intro j
  exact hF j _ (hf j)

end IsInvertedBy

def FunctorsInverting (W : MorphismProperty C) (D : Type*) [Category* D] :=
  ObjectProperty.FullSubcategory fun F : C ⥤ D => W.IsInvertedBy F
