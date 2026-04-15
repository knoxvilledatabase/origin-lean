/-
Extracted from CategoryTheory/Adjunction/Limits.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Adjunctions and limits

A left adjoint preserves colimits (`CategoryTheory.Adjunction.leftAdjoint_preservesColimits`),
and a right adjoint preserves limits (`CategoryTheory.Adjunction.rightAdjoint_preservesLimits`).

Equivalences create and reflect (co)limits.
(`CategoryTheory.Functor.createsLimitsOfIsEquivalence`,
`CategoryTheory.Functor.createsColimitsOfIsEquivalence`,
`CategoryTheory.Functor.reflectsLimits_of_isEquivalence`,
`CategoryTheory.Functor.reflectsColimits_of_isEquivalence`.)

In `CategoryTheory.Adjunction.coconesIso` we show that
when `F ⊣ G`,
the functor associating to each `Y` the cocones over `K ⋙ F` with cone point `Y`
is naturally isomorphic to
the functor associating to each `Y` the cocones over `K` with cone point `G.obj Y`.
-/

open Opposite

namespace CategoryTheory

open Functor Limits

universe v u v₁ v₂ v₀ u₁ u₂

namespace Adjunction

section ArbitraryUniverse

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)

section PreservationColimits

variable {J : Type u} [Category.{v} J] (K : J ⥤ C)

def functorialityRightAdjoint : Cocone (K ⋙ F) ⥤ Cocone K :=
  Cocone.functoriality _ G ⋙
    Cocone.precompose (K.rightUnitor.inv ≫ whiskerLeft K adj.unit ≫ (associator _ _ _).inv)

attribute [local simp] functorialityRightAdjoint

set_option backward.isDefEq.respectTransparency false in
