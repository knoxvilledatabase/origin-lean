/-
Extracted from CategoryTheory/Enriched/Limits/HasConicalProducts.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Existence of conical products
-/

universe w v' v u u'

namespace CategoryTheory.Enriched

open Limits

class HasConicalProducts
    (V : outParam <| Type u') [Category.{v'} V] [MonoidalCategory V]
    (C : Type u) [Category.{v} C] [EnrichedOrdinaryCategory V C] : Prop where
  /-- A family of objects (parametrized by any `J : Type w`) has a conical product. -/
  hasConicalLimitsOfShape : ∀ J : Type w, HasConicalLimitsOfShape (Discrete J) V C := by
    infer_instance

attribute [instance] HasConicalProducts.hasConicalLimitsOfShape

variable (V : Type u') [Category.{v'} V] [MonoidalCategory V]

variable {C : Type u} [Category.{v} C] [EnrichedOrdinaryCategory V C]

abbrev HasConicalProduct {I : Type w} (f : I → C) :=
  HasConicalLimit V (Discrete.functor f)

example [HasConicalProducts.{w} V C] : HasProducts.{w} C := inferInstance

end CategoryTheory.Enriched
