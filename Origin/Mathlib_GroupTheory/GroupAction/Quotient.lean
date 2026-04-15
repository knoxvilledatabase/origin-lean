/-
Extracted from GroupTheory/GroupAction/Quotient.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Properties of group actions involving quotient groups

This file proves properties of group actions which use the quotient group construction, notably
* the orbit-stabilizer theorem `MulAction.card_orbit_mul_card_stabilizer_eq_card_group`
* the class formula `MulAction.selfEquivSigmaOrbitsQuotientStabilizer'`
* Burnside's lemma `MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group`,

as well as their analogues for additive groups.
-/

assert_not_exists Cardinal

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

open Function

open scoped commutatorElement

namespace MulAction

variable [Group α]

section QuotientAction

open Subgroup MulOpposite QuotientGroup

variable (β) [Monoid β] [MulAction β α] (H : Subgroup α)

class QuotientAction : Prop where
  /-- The action fulfils a normality condition on products that lie in `H`.
    This ensures that the action descends to an action on the quotient `α ⧸ H`. -/
  inv_mul_mem : ∀ (b : β) {a a' : α}, a⁻¹ * a' ∈ H → (b • a)⁻¹ * b • a' ∈ H

class _root_.AddAction.QuotientAction {α : Type u} (β : Type v) [AddGroup α] [AddMonoid β]
  [AddAction β α] (H : AddSubgroup α) : Prop where
  /-- The action fulfils a normality condition on summands that lie in `H`.
    This ensures that the action descends to an action on the quotient `α ⧸ H`. -/
  inv_mul_mem : ∀ (b : β) {a a' : α}, -a + a' ∈ H → -(b +ᵥ a) + (b +ᵥ a') ∈ H

attribute [to_additive] MulAction.QuotientAction
