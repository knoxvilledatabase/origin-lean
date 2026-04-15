/-
Extracted from MeasureTheory/Function/SimpleFuncDense.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Density of simple functions

Show that each Borel measurable function can be approximated pointwise
by a sequence of simple functions.

## Main definitions

* `MeasureTheory.SimpleFunc.nearestPt (e : ℕ → α) (N : ℕ) : α →ₛ ℕ`: the `SimpleFunc` sending
  each `x : α` to the point `e k` which is the nearest to `x` among `e 0`, ..., `e N`.
* `MeasureTheory.SimpleFunc.approxOn (f : β → α) (hf : Measurable f) (s : Set α) (y₀ : α)
  (h₀ : y₀ ∈ s) [SeparableSpace s] (n : ℕ) : β →ₛ α` : a simple function that takes values in `s`
  and approximates `f`.

## Main results

* `tendsto_approxOn` (pointwise convergence): If `f x ∈ s`, then the sequence of simple
  approximations `MeasureTheory.SimpleFunc.approxOn f hf s y₀ h₀ n`, evaluated at `x`,
  tends to `f x` as `n` tends to `∞`.

## Notation

* `α →ₛ β` (local notation): the type of simple functions `α → β`.
-/

open Set Function Filter TopologicalSpace Metric MeasureTheory

open scoped Topology ENNReal

variable {α β : Type*}

noncomputable section

namespace MeasureTheory

local infixr:25 " →ₛ " => SimpleFunc

namespace SimpleFunc

/-! ### Pointwise approximation by simple functions -/

variable [MeasurableSpace α] [PseudoEMetricSpace α] [OpensMeasurableSpace α]

noncomputable def nearestPtInd (e : ℕ → α) : ℕ → α →ₛ ℕ
  | 0 => const α 0
  | N + 1 =>
    piecewise (⋂ k ≤ N, { x | edist (e (N + 1)) x < edist (e k) x })
      (MeasurableSet.iInter fun _ =>
        MeasurableSet.iInter fun _ =>
          measurableSet_lt measurable_edist_right measurable_edist_right)
      (const α <| N + 1) (nearestPtInd e N)

noncomputable def nearestPt (e : ℕ → α) (N : ℕ) : α →ₛ α :=
  (nearestPtInd e N).map e
