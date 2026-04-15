/-
Extracted from CategoryTheory/Preadditive/Projective/Basic.lean
Genuine: 6 of 6 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Projective objects and categories with enough projectives

An object `P` is called *projective* if every morphism out of `P` factors through every epimorphism.

A category `C` *has enough projectives* if every object admits an epimorphism from some
projective object.

`CategoryTheory.Projective.over X` picks an arbitrary such projective object, and
`CategoryTheory.Projective.π X : CategoryTheory.Projective.over X ⟶ X` is the corresponding
epimorphism.

Given a morphism `f : X ⟶ Y`, `CategoryTheory.Projective.left f` is a projective object over
`CategoryTheory.Limits.kernel f`, and `Projective.d f : Projective.left f ⟶ X` is the morphism
`π (kernel f) ≫ kernel.ι f`.

-/

noncomputable section

open CategoryTheory Limits Opposite

universe v u v' u'

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

class Projective (P : C) : Prop where
  factors : ∀ {E X : C} (f : P ⟶ X) (e : E ⟶ X) [Epi e], ∃ f', f' ≫ e = f

variable (C) in

abbrev isProjective : ObjectProperty C := Projective

lemma Limits.IsZero.projective {X : C} (h : IsZero X) : Projective X where
  factors _ _ _ := ⟨h.to_ _, h.eq_of_src _ _⟩

structure ProjectivePresentation (X : C) where
  /-- The projective object `p` of this presentation -/
  p : C
  [projective : Projective p]
  /-- The epimorphism from `p` of this presentation -/
  f : p ⟶ X
  [epi : Epi f]

attribute [instance] ProjectivePresentation.projective ProjectivePresentation.epi

variable (C)

class EnoughProjectives : Prop where
  presentation : ∀ X : C, Nonempty (ProjectivePresentation X)

end

namespace Projective

def factorThru {P X E : C} [Projective P] (f : P ⟶ X) (e : E ⟶ X) [Epi e] : P ⟶ E :=
  (Projective.factors f e).choose
