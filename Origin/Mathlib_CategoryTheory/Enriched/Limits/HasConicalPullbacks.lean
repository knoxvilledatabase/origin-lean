/-
Extracted from CategoryTheory/Enriched/Limits/HasConicalPullbacks.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Existence of conical pullbacks
-/

universe w v' v u u'

namespace CategoryTheory.Enriched

open Limits

variable (V : Type u') [Category.{v'} V] [MonoidalCategory V]

variable {C : Type u} [Category.{v} C] [EnrichedOrdinaryCategory V C]

abbrev HasConicalPullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :=
  HasConicalLimit V (cospan f g)

example {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasConicalPullback V f g] : HasPullback f g :=

  inferInstance

variable (C)

abbrev HasConicalPullbacks : Prop := HasConicalLimitsOfShape WalkingCospan V C

example [HasConicalPullbacks V C] : HasPullbacks C := inferInstance

end CategoryTheory.Enriched
