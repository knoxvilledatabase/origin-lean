/-
Extracted from SetTheory/Cardinal/Cofinality.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Cofinality

This file contains the definition of cofinality of an order and an ordinal number.

## Main Definitions

* `Order.cof α` is the cofinality of a preorder. This is the smallest cardinality of a cofinal
  subset.
* `Ordinal.cof o` is the cofinality of the ordinal `o` when viewed as a linear order.

## Main Statements

* `Cardinal.lt_power_cof_ord`: A consequence of König's theorem stating that `c < c ^ c.ord.cof` for
  `c ≥ ℵ₀`.

## Implementation Notes

* The cofinality is defined for ordinals.
  If `c` is a cardinal number, its cofinality is `c.ord.cof`.
-/

public noncomputable section

open Function Cardinal Set Order

open scoped Ordinal

universe u v w

variable {α γ : Type u} {β : Type v}

/-! ### Cofinality of orders -/

namespace Order

section Preorder

variable [Preorder α]

variable (α) in

def cof : Cardinal :=
  ⨅ s : {s : Set α // IsCofinal s}, #s

theorem cof_le {s : Set α} (h : IsCofinal s) : cof α ≤ #s :=
  ciInf_le' (ι := {s : Set α // IsCofinal s}) _ ⟨s, h⟩

theorem le_lift_cof_iff {c : Cardinal.{max u v}} :
    c ≤ lift.{v} (cof α) ↔ ∀ s : Set α, IsCofinal s → c ≤ lift.{v} #s := by
  rw [cof, lift_iInf, le_ciInf_iff']
  simp

theorem le_cof_iff {c : Cardinal} : c ≤ cof α ↔ ∀ s : Set α, IsCofinal s → c ≤ #s := by
  simpa using @le_lift_cof_iff.{u, u} α _ c
