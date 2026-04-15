/-
Extracted from MeasureTheory/Function/SimpleFunc.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Simple functions

A function `f` from a measurable space to any type is called *simple*, if every preimage `f ⁻¹' {x}`
is measurable, and the range is finite. In this file, we define simple functions and establish their
basic properties; and we construct a sequence of simple functions approximating an arbitrary Borel
measurable function `f : α → ℝ≥0∞`.

The theorem `Measurable.ennreal_induction` shows that in order to prove something for an arbitrary
measurable function into `ℝ≥0∞`, it is sufficient to show that the property holds for (multiples of)
characteristic functions and is closed under addition and supremum of increasing sequences of
functions.
-/

noncomputable section

open Set hiding restrict restrict_apply

open Filter ENNReal

open Function (support)

open Topology NNReal ENNReal MeasureTheory

namespace MeasureTheory

variable {α β γ δ : Type*}

structure SimpleFunc.{u, v} (α : Type u) [MeasurableSpace α] (β : Type v) where
  /-- The underlying function -/
  toFun : α → β
  measurableSet_fiber' : ∀ x, MeasurableSet (toFun ⁻¹' {x})
  finite_range' : (Set.range toFun).Finite

local infixr:25 " →ₛ " => SimpleFunc

namespace SimpleFunc

section Measurable

variable [MeasurableSpace α]

-- INSTANCE (free from Core): instFunLike

theorem coe_injective ⦃f g : α →ₛ β⦄ (H : (f : α → β) = g) : f = g := DFunLike.ext' H
