/-
Extracted from CategoryTheory/Preadditive/Injective/Basic.lean
Genuine: 6 of 6 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Injective objects and categories with enough injectives

An object `J` is injective iff every morphism into `J` can be obtained by extending a monomorphism.
-/

noncomputable section

open CategoryTheory Limits Opposite

universe v v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]

class Injective (J : C) : Prop where
  factors : ∀ {X Y : C} (g : X ⟶ J) (f : X ⟶ Y) [Mono f], ∃ h : Y ⟶ J, f ≫ h = g

attribute [inherit_doc Injective] Injective.factors

variable (C) in

abbrev isInjective : ObjectProperty C := Injective

lemma Limits.IsZero.injective {X : C} (h : IsZero X) : Injective X where
  factors _ _ _ := ⟨h.from_ _, h.eq_of_tgt _ _⟩

structure InjectivePresentation (X : C) where
  J : C
  injective : Injective J := by infer_instance
  f : X ⟶ J
  mono : Mono f := by infer_instance

open InjectivePresentation in

attribute [inherit_doc InjectivePresentation] J injective f mono

attribute [instance] InjectivePresentation.injective InjectivePresentation.mono

variable (C)

class EnoughInjectives : Prop where
  presentation : ∀ X : C, Nonempty (InjectivePresentation X)

attribute [inherit_doc EnoughInjectives] EnoughInjectives.presentation

end

namespace Injective

def factorThru {J X Y : C} [Injective J] (g : X ⟶ J) (f : X ⟶ Y) [Mono f] : Y ⟶ J :=
  (Injective.factors g f).choose
