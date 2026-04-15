/-
Extracted from CategoryTheory/Enriched/Limits/HasConicalTerminal.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Existence of conical terminal objects
-/

universe w v' v u u'

namespace CategoryTheory.Enriched

open Limits HasConicalLimit

abbrev HasConicalTerminal := HasConicalLimitsOfShape (Discrete.{0} PEmpty)

variable (V : Type u') [Category.{v'} V] [MonoidalCategory V]

variable (C : Type u) [Category.{v} C] [EnrichedOrdinaryCategory V C]

example [HasConicalTerminal V C] : HasTerminal C := inferInstance

-- INSTANCE (free from Core): HasConicalProducts.hasConicalTerminal

end CategoryTheory.Enriched
