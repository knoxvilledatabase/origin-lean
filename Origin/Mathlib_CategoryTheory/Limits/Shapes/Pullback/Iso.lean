/-
Extracted from CategoryTheory/Limits/Shapes/Pullback/Iso.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The pullback of an isomorphism

This file provides some basic results about the pullback (and pushout) of an isomorphism.

-/

noncomputable section

open CategoryTheory

universe w v₁ v₂ v u u₂

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {X Y Z : C}

section PullbackLeftIso

open WalkingCospan

variable (f : X ⟶ Z) (g : Y ⟶ Z) [IsIso f]

def pullbackConeOfLeftIso : PullbackCone f g :=
  PullbackCone.mk (g ≫ inv f) (𝟙 _) <| by simp
