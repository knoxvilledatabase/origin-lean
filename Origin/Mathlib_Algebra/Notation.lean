/-
Extracted from Algebra/Notation.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Notations for operations involving order and algebraic structure

## Notation

* `a⁺ᵐ = a ⊔ 1`: *Positive component* of an element `a` of a multiplicative lattice ordered group
* `a⁻ᵐ = a⁻¹ ⊔ 1`: *Negative component* of an element `a` of a multiplicative lattice ordered group
* `a⁺ = a ⊔ 0`: *Positive component* of an element `a` of a lattice ordered group
* `a⁻ = (-a) ⊔ 0`: *Negative component* of an element `a` of a lattice ordered group
-/

class PosPart (α : Type*) where
  /-- The *positive part* of an element `a`. -/
  posPart : α → α
