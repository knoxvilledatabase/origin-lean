/-
Extracted from Combinatorics/Quiver/ReflQuiver.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Reflexive Quivers

This module defines reflexive quivers. A reflexive quiver, or "refl quiver" for short, extends
a quiver with a specified endoarrow on each term in its type of objects.

We also introduce morphisms between reflexive quivers, called reflexive prefunctors or "refl
prefunctors" for short.

Note: Currently Category does not extend ReflQuiver, although it could. (TODO: do this)
-/

namespace CategoryTheory

universe v v₁ v₂ u u₁ u₂

class ReflQuiver (obj : Type u) : Type max u (v + 1) extends Quiver.{v} obj where
  /-- The identity morphism on an object. -/
  id : ∀ X : obj, Hom X X

scoped notation "𝟙rq" => ReflQuiver.id  -- type as \b1
