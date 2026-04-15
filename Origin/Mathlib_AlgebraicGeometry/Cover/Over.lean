/-
Extracted from AlgebraicGeometry/Cover/Over.lean
Genuine: 3 of 4 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!

# Covers of schemes over a base

In this file we define the typeclass `Cover.Over`. For a cover `𝒰` of an `S`-scheme `X`,
the datum `𝒰.Over S` contains `S`-scheme structures on the components of `𝒰` and asserts
that the component maps are morphisms of `S`-schemes.

We provide instances of `𝒰.Over S` for standard constructions on covers.

-/

universe v u

noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {P : MorphismProperty Scheme.{u}} (S : Scheme.{u})

abbrev asOverProp (X : Scheme.{u}) (S : Scheme.{u}) [X.Over S] (h : P (X ↘ S)) : P.Over ⊤ S :=
  ⟨X.asOver S, h⟩

abbrev Hom.asOverProp {X Y : Scheme.{u}} (f : X.Hom Y) (S : Scheme.{u}) [X.Over S] [Y.Over S]
    [f.IsOver S] {hX : P (X ↘ S)} {hY : P (Y ↘ S)} : X.asOverProp S hX ⟶ Y.asOverProp S hY :=
  ⟨f.asOver S, trivial, trivial⟩

protected class Cover.Over {P : MorphismProperty Scheme.{u}} [P.IsStableUnderBaseChange]
    [IsJointlySurjectivePreserving P] {X : Scheme.{u}} [X.Over S]
    (𝒰 : X.Cover (precoverage P)) where
  over (j : 𝒰.I₀) : (𝒰.X j).Over S := by infer_instance
  isOver_map (j : 𝒰.I₀) : (𝒰.f j).IsOver S := by infer_instance

attribute [instance_reducible] Cover.Over.over

attribute [instance] Cover.Over.over Cover.Over.isOver_map

variable [P.IsStableUnderBaseChange] [IsJointlySurjectivePreserving P]

-- INSTANCE (free from Core): [P.ContainsIdentities]

variable {X W : Scheme.{u}} (𝒰 : X.Cover (precoverage P)) (f : W ⟶ X) [W.Over S] [X.Over S]
  [𝒰.Over S] [f.IsOver S]

set_option backward.isDefEq.respectTransparency false in
