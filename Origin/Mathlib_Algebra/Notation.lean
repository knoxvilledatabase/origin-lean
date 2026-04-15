/-
Extracted from Algebra/Notation.lean
Genuine: 4 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ToAdditive

/-!
# Notations for operations involving order and algebraic structure

## Notations

* `a⁺ᵐ = a ⊔ 1`: *Positive component* of an element `a` of a multiplicative lattice ordered group
* `a⁻ᵐ = a⁻¹ ⊔ 1`: *Negative component* of an element `a` of a multiplicative lattice ordered group
* `a⁺ = a ⊔ 0`: *Positive component* of an element `a` of a lattice ordered group
* `a⁻ = (-a) ⊔ 0`: *Negative component* of an element `a` of a lattice ordered group
-/

class PosPart (α : Type*) where
  /-- The *positive part* of an element `a`. -/
  posPart : α → α

@[to_additive]
class OneLePart (α : Type*) where
  /-- The *positive part* of an element `a`. -/
  oneLePart : α → α

class NegPart (α : Type*) where
  /-- The *negative part* of an element `a`. -/
  negPart : α → α

@[to_additive]
class LeOnePart (α : Type*) where
  /-- The *negative part* of an element `a`. -/
  leOnePart : α → α

export OneLePart (oneLePart)

export LeOnePart (leOnePart)

export PosPart (posPart)

export NegPart (negPart)
