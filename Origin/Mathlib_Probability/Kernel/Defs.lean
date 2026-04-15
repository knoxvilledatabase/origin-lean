/-
Extracted from Probability/Kernel/Defs.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Markov Kernels

A kernel from a measurable space `α` to another measurable space `β` is a measurable map
`α → MeasureTheory.Measure β`, where the measurable space instance on `measure β` is the one defined
in `MeasureTheory.Measure.instMeasurableSpace`. That is, a kernel `κ` verifies that for all
measurable sets `s` of `β`, `a ↦ κ a s` is measurable.

## Main definitions

Classes of kernels:
* `ProbabilityTheory.Kernel α β`: kernels from `α` to `β`.
* `ProbabilityTheory.IsMarkovKernel κ`: a kernel from `α` to `β` is said to be a Markov kernel
  if for all `a : α`, `k a` is a probability measure.
* `ProbabilityTheory.IsZeroOrMarkovKernel κ`: a kernel from `α` to `β` which is zero or
  a Markov kernel.
* `ProbabilityTheory.IsFiniteKernel κ`: a kernel from `α` to `β` is said to be finite if there
  exists `C : ℝ≥0∞` such that `C < ∞` and for all `a : α`, `κ a univ ≤ C`. This implies in
  particular that all measures in the image of `κ` are finite, but is stronger since it requires a
  uniform bound. This stronger condition is necessary to ensure that the composition of two finite
  kernels is finite.
* `ProbabilityTheory.IsSFiniteKernel κ`: a kernel is called s-finite if it is a countable
  sum of finite kernels.

## Main statements

* `ProbabilityTheory.Kernel.ext_fun`: if `∫⁻ b, f b ∂(κ a) = ∫⁻ b, f b ∂(η a)` for all measurable
  functions `f` and all `a`, then the two kernels `κ` and `η` are equal.

-/

assert_not_exists MeasureTheory.integral

open MeasureTheory

open scoped ENNReal

namespace ProbabilityTheory

structure Kernel (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] where
  /-- The underlying function of a kernel.

  Do not use this function directly. Instead use the coercion coming from the `DFunLike`
  instance. -/
  toFun : α → Measure β
  /-- A kernel is a measurable map.

  Do not use this lemma directly. Use `Kernel.measurable` instead. -/
  measurable' : Measurable toFun

scoped notation "Kernel[" mα "] " α:arg β:arg => @Kernel α β mα _

scoped notation "Kernel[" mα ", " mβ "] " α:arg β:arg => @Kernel α β mα mβ

variable {α β ι : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}

namespace Kernel

-- INSTANCE (free from Core): instFunLike
