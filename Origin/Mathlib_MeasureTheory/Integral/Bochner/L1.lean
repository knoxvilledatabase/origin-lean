/-
Extracted from MeasureTheory/Integral/Bochner/L1.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Bochner integral

The Bochner integral extends the definition of the Lebesgue integral to functions that map from a
measure space into a Banach space (complete normed vector space). It is constructed here
for L1 functions by extending the integral on simple functions. See the file
`Mathlib/MeasureTheory/Integral/Bochner/Basic.lean` for the integral of functions
and corresponding API.

## Main definitions

The Bochner integral is defined through the extension process described in the file
`Mathlib/MeasureTheory/Integral/SetToL1.lean`, which follows these steps:

1. Define the integral of the indicator of a set. This is `weightedSMul μ s x = μ.real s • x`.
  `weightedSMul μ` is shown to be linear in the value `x` and `DominatedFinMeasAdditive`
  (defined in the file `Mathlib/MeasureTheory/Integral/SetToL1.lean`) with respect to the set `s`.

2. Define the integral on simple functions of the type `SimpleFunc α E` (notation : `α →ₛ E`)
  where `E` is a real normed space. (See `SimpleFunc.integral` for details.)

3. Transfer this definition to define the integral on `L1.simpleFunc α E` (notation :
  `α →₁ₛ[μ] E`), see `L1.simpleFunc.integral`. Show that this integral is a continuous linear
  map from `α →₁ₛ[μ] E` to `E`.

4. Define the Bochner integral on L1 functions by extending the integral on integrable simple
  functions `α →₁ₛ[μ] E` using `ContinuousLinearMap.extend` and the fact that the embedding of
  `α →₁ₛ[μ] E` into `α →₁[μ] E` is dense.

## Notation

* `α →ₛ E` : simple functions (defined in `Mathlib/MeasureTheory/Function/SimpleFunc.lean`)
* `α →₁[μ] E` : functions in L1 space, i.e., equivalence classes of integrable functions (defined in
                `Mathlib/MeasureTheory/Function/LpSpace/Basic.lean`)
* `α →₁ₛ[μ] E` : simple functions in L1 space, i.e., equivalence classes of integrable simple
                 functions (defined in `Mathlib/MeasureTheory/Function/SimpleFuncDenseLp.lean`)

Note: `ₛ` is typed using `\_s`. Sometimes it shows as a box if the font is missing.

## Tags

Bochner integral, simple function, function space, Lebesgue dominated convergence theorem

-/

assert_not_exists Differentiable

noncomputable section

open Filter ENNReal Set

open scoped NNReal ENNReal MeasureTheory

namespace MeasureTheory

variable {α E F 𝕜 : Type*}

section WeightedSMul

open ContinuousLinearMap

variable [NormedAddCommGroup F] [NormedSpace ℝ F] {m : MeasurableSpace α} {μ : Measure α}

def weightedSMul {_ : MeasurableSpace α} (μ : Measure α) (s : Set α) : F →L[ℝ] F :=
  μ.real s • ContinuousLinearMap.id ℝ F

theorem weightedSMul_apply {m : MeasurableSpace α} (μ : Measure α) (s : Set α) (x : F) :
    weightedSMul μ s x = μ.real s • x := by simp [weightedSMul]
