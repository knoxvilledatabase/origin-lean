/-
Extracted from Combinatorics/Quiver/Basic.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Quivers

This module defines quivers. A quiver on a type `V` of vertices assigns to every
pair `a b : V` of vertices a type `a ⟶ b` of arrows from `a` to `b`. This
is a generalization of `Digraph V`, which can be thought of as "a proposition `a ⟶ b` of arrows".

-/

open Opposite

universe v v₁ v₂ u u₁ u₂

class Quiver (V : Type u) where
  /-- The type of edges/arrows/morphisms between a given source and target. -/
  Hom : V → V → Type v

attribute [to_dual self (reorder := 3 4)] Quiver.Hom

attribute [to_dual self (reorder := Hom (1 2))] Quiver.mk

infixr:10 " ⟶ " => Quiver.Hom

namespace Quiver

-- INSTANCE (free from Core): opposite
