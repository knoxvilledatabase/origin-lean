/-
Extracted from MeasureTheory/Order/Lattice.lean
Genuine: 4 of 8 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# Typeclasses for measurability of lattice operations

In this file we define classes `MeasurableSup` and `MeasurableInf` and prove dot-style
lemmas (`Measurable.sup`, `AEMeasurable.sup` etc). For binary operations we define two typeclasses:

- `MeasurableSup` says that both left and right sup are measurable;
- `MeasurableSup₂` says that `fun p : α × α => p.1 ⊔ p.2` is measurable,

and similarly for other binary operations. The reason for introducing these classes is that in case
of topological space `α` equipped with the Borel `σ`-algebra, instances for `MeasurableSup₂`
etc. require `α` to have a second countable topology.

For instances relating, e.g., `ContinuousSup` to `MeasurableSup` see file
`MeasureTheory.BorelSpace`.

## Tags

measurable function, lattice operation

-/

open MeasureTheory

class MeasurableSup (M : Type*) [MeasurableSpace M] [Max M] : Prop where
  measurable_const_sup : ∀ c : M, Measurable (c ⊔ ·) := by intro c; fun_prop
  measurable_sup_const : ∀ c : M, Measurable (· ⊔ c) := by intro c; fun_prop

class MeasurableSup₂ (M : Type*) [MeasurableSpace M] [Max M] : Prop where
  measurable_sup : Measurable fun p : M × M => p.1 ⊔ p.2 := by intro p; fun_prop

export MeasurableSup₂ (measurable_sup)

export MeasurableSup (measurable_const_sup measurable_sup_const)

class MeasurableInf (M : Type*) [MeasurableSpace M] [Min M] : Prop where
  measurable_const_inf : ∀ c : M, Measurable (c ⊓ ·) := by intro c; fun_prop
  measurable_inf_const : ∀ c : M, Measurable (· ⊓ c) := by intro c; fun_prop

class MeasurableInf₂ (M : Type*) [MeasurableSpace M] [Min M] : Prop where
  measurable_inf : Measurable fun p : M × M => p.1 ⊓ p.2 := by intro p; fun_prop

export MeasurableInf₂ (measurable_inf)

export MeasurableInf (measurable_const_inf measurable_inf_const)

variable {M : Type*} [MeasurableSpace M]

section OrderDual

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): (priority

end OrderDual

variable {α : Type*} {m : MeasurableSpace α} {μ : Measure α} {f g : α → M}

section Sup

variable [Max M]

section MeasurableSup

variable [MeasurableSup M]
