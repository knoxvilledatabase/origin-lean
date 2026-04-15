/-
Extracted from Combinatorics/Quiver/Prefunctor.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Morphisms of quivers
-/

universe v₁ v₂ u u₁ u₂

structure Prefunctor (V : Type u₁) [Quiver.{v₁} V] (W : Type u₂) [Quiver.{v₂} W] where
  /-- The action of a (pre)functor on vertices/objects. -/
  obj : V → W
  /-- The action of a (pre)functor on edges/arrows/morphisms. -/
  map : ∀ {X Y : V}, (X ⟶ Y) → (obj X ⟶ obj Y)

attribute [to_dual self] Prefunctor.map

namespace Prefunctor
