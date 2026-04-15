/-
Extracted from MeasureTheory/Group/Arithmetic.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Typeclasses for measurability of operations

In this file we define classes `MeasurableMul` etc. and prove dot-style lemmas
(`Measurable.mul`, `AEMeasurable.mul` etc). For binary operations we define two typeclasses:

- `MeasurableMul` says that both left and right multiplication are measurable;
- `MeasurableMul₂` says that `fun p : α × α => p.1 * p.2` is measurable,

and similarly for other binary operations. The reason for introducing these classes is that in case
of topological space `α` equipped with the Borel `σ`-algebra, instances for `MeasurableMul₂`
etc. require `α` to have a second countable topology.

We define separate classes for `MeasurableDiv`/`MeasurableSub`
because on some types (e.g., `ℕ`, `ℝ≥0∞`) division and/or subtraction are not defined as `a * b⁻¹` /
`a + (-b)`.

For instances relating, e.g., `ContinuousMul` to `MeasurableMul` see file
`MeasureTheory.BorelSpace`.

## Implementation notes

For the heuristics of `@[to_additive]` it is important that the type with a multiplication
(or another multiplicative operation) is the first (implicit) argument of all declarations.

## Tags

measurable function, arithmetic operator

## TODO

* Uniformize the treatment of `pow` and `smul`.
* Use `@[to_additive]` to send `MeasurablePow` to `MeasurableSMul₂`.
* This might require changing the definition (swapping the arguments in the function that is
  in the conclusion of `MeasurableSMul`.)
-/

open MeasureTheory

open scoped Pointwise

universe u v

variable {α : Type*}

/-!
### Binary operations: `(· + ·)`, `(· * ·)`, `(· - ·)`, `(· / ·)`
-/

class MeasurableAdd (M : Type*) [MeasurableSpace M] [Add M] : Prop where
  measurable_const_add : ∀ c : M, Measurable (c + ·) := by intro; fun_prop
  measurable_add_const : ∀ c : M, Measurable (· + c) := by intro; fun_prop

export MeasurableAdd (measurable_const_add measurable_add_const)

class MeasurableAdd₂ (M : Type*) [MeasurableSpace M] [Add M] : Prop where
  measurable_add : Measurable fun p : M × M => p.1 + p.2

export MeasurableAdd₂ (measurable_add)
