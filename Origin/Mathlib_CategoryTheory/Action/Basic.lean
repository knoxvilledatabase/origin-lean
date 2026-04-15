/-
Extracted from CategoryTheory/Action/Basic.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# `Action V G`, the category of actions of a monoid `G` inside some category `V`.

The prototypical example is `V = ModuleCat R`,
where `Action (ModuleCat R) G` is the category of `R`-linear representations of `G`.

We check `Action V G ≌ (CategoryTheory.SingleObj G ⥤ V)`,
and construct the restriction functors
`res {G H} [Monoid G] [Monoid H] (f : G →* H) : Action V H ⥤ Action V G`.
-/

universe u v

open CategoryTheory Limits

variable (V : Type*) [Category* V]

structure Action (G : Type*) [Monoid G] where
  /-- The object this action acts on -/
  V : V
  /-- The underlying monoid homomorphism of this action -/
  ρ : G →* End V

namespace Action

variable {V}
