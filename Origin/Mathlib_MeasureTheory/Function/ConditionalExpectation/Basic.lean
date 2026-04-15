/-
Extracted from MeasureTheory/Function/ConditionalExpectation/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! # Conditional expectation

We build the conditional expectation of an integrable function `f` with value in a Banach space
with respect to a measure `μ` (defined on a measurable space structure `m₀`) and a measurable space
structure `m` with `hm : m ≤ m₀` (a sub-sigma-algebra). This is an `m`-strongly measurable
function `μ[f|hm]` which is integrable and verifies `∫ x in s, μ[f|hm] x ∂μ = ∫ x in s, f x ∂μ`
for all `m`-measurable sets `s`. It is unique as an element of `L¹`.

The construction is done in four steps:
* Define the conditional expectation of an `L²` function, as an element of `L²`. This is the
  orthogonal projection on the subspace of almost everywhere `m`-measurable functions.
* Show that the conditional expectation of the indicator of a measurable set with finite measure
  is integrable and define a map `Set α → (E →L[ℝ] (α →₁[μ] E))` which to a set associates a linear
  map. That linear map sends `x ∈ E` to the conditional expectation of the indicator of the set
  with value `x`.
* Extend that map to `condExpL1CLM : (α →₁[μ] E) →L[ℝ] (α →₁[μ] E)`. This is done using the same
  construction as the Bochner integral (see the file `MeasureTheory/Integral/SetToL1`).
* Define the conditional expectation of a function `f : α → E`, which is an integrable function
  `α → E` equal to 0 if `f` is not integrable, and equal to an `m`-measurable representative of
  `condExpL1CLM` applied to `[f]`, the equivalence class of `f` in `L¹`.

The first step is done in `MeasureTheory.Function.ConditionalExpectation.CondexpL2`, the two
next steps in `MeasureTheory.Function.ConditionalExpectation.CondexpL1` and the final step is
performed in this file.

## Main results

The conditional expectation and its properties

* `condExp (m : MeasurableSpace α) (μ : Measure α) (f : α → E)`: conditional expectation of `f`
  with respect to `m`.
* `integrable_condExp` : `condExp` is integrable.
* `stronglyMeasurable_condExp` : `condExp` is `m`-strongly-measurable.
* `setIntegral_condExp (hf : Integrable f μ) (hs : MeasurableSet[m] s)` : if `m ≤ m₀` (the
  σ-algebra over which the measure is defined), then the conditional expectation verifies
  `∫ x in s, condExp m μ f x ∂μ = ∫ x in s, f x ∂μ` for any `m`-measurable set `s`.

While `condExp` is function-valued, we also define `condExpL1` with value in `L1` and a continuous
linear map `condExpL1CLM` from `L1` to `L1`. `condExp` should be used in most cases.

Uniqueness of the conditional expectation

* `ae_eq_condExp_of_forall_setIntegral_eq`: an a.e. `m`-measurable function which verifies the
  equality of integrals is a.e. equal to `condExp`.

## Notation

For a measure `μ` defined on a measurable space structure `m₀`, another measurable space structure
`m` with `hm : m ≤ m₀` (a sub-σ-algebra) and a function `f`, we define the notation
* `μ[f | m] = condExp m μ f`.

## TODO

See https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/Conditional.20expectation.20of.20product
for how to prove that we can pull `m`-measurable continuous linear maps out of the `m`-conditional
expectation. This would generalise `MeasureTheory.condExp_mul_of_stronglyMeasurable_left`.

## Tags

conditional expectation, conditional expected value

-/

open TopologicalSpace MeasureTheory.Lp Filter

open scoped ENNReal Topology MeasureTheory

namespace MeasureTheory

variable {α β E 𝕜 : Type*} [RCLike 𝕜] {m m₀ : MeasurableSpace α} {μ : Measure α} {f g : α → E}
  {s : Set α}

section NormedAddCommGroup

variable [NormedAddCommGroup E] [CompleteSpace E]

section NormedSpace

variable [NormedSpace ℝ E]

open scoped Classical in

variable (m) in

noncomputable irreducible_def condExp (μ : Measure[m₀] α) (f : α → E) : α → E :=
  if hm : m ≤ m₀ then
    if h : SigmaFinite (μ.trim hm) ∧ Integrable f μ then
      if StronglyMeasurable[m] f then f
      else have := h.1; aestronglyMeasurable_condExpL1.mk (condExpL1 hm μ f)
    else 0
  else 0
