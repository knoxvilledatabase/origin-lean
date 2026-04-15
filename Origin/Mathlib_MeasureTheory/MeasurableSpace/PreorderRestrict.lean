/-
Extracted from MeasureTheory/MeasurableSpace/PreorderRestrict.lean
Genuine: 4 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Order.Restriction
import Mathlib.MeasureTheory.MeasurableSpace.Basic

/-!
# Measurability of the restriction function for functions indexed by a preorder

We prove that the map which restricts a function `f : (i : α) → X i` to elements `≤ a` is
measurable.
-/

open MeasureTheory

namespace Preorder

variable {α : Type*} [Preorder α] {X : α → Type*} [∀ a, MeasurableSpace (X a)]

@[measurability, fun_prop]
theorem measurable_restrictLe (a : α) : Measurable (restrictLe (π := X) a) :=
    Set.measurable_restrict _

@[measurability, fun_prop]
theorem measurable_restrictLe₂ {a b : α} (hab : a ≤ b) : Measurable (restrictLe₂ (π := X) hab) :=
  Set.measurable_restrict₂ _

variable [LocallyFiniteOrderBot α]

@[measurability, fun_prop]
theorem measurable_frestrictLe (a : α) : Measurable (frestrictLe (π := X) a) :=
  Finset.measurable_restrict _

@[measurability, fun_prop]
theorem measurable_frestrictLe₂ {a b : α} (hab : a ≤ b) : Measurable (frestrictLe₂ (π := X) hab) :=
  Finset.measurable_restrict₂ _

end Preorder
