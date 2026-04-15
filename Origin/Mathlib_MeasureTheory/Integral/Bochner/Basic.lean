/-
Extracted from MeasureTheory/Integral/Bochner/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Bochner integral

The Bochner integral extends the definition of the Lebesgue integral to functions that map from a
measure space into a Banach space (complete normed vector space). It is constructed here using
the L1 Bochner integral constructed in the file `Mathlib/MeasureTheory/Integral/Bochner/L1.lean`.

## Main definitions

The Bochner integral is defined through the extension process described in the file
`Mathlib/MeasureTheory/Integral/SetToL1.lean`, which follows these steps:

* `MeasureTheory.integral`: the Bochner integral on functions defined as the Bochner integral of
  its equivalence class in L1 space, if it is in L1, and 0 otherwise.

The result of that construction is `∫ a, f a ∂μ`, which is definitionally equal to
`setToFun (dominatedFinMeasAdditive_weightedSMul μ) f`. Some basic properties of the integral
(like linearity) are particular cases of the properties of `setToFun` (which are described in the
file `Mathlib/MeasureTheory/Integral/SetToL1.lean`).

## Main statements

1. Basic properties of the Bochner integral on functions of type `α → E`, where `α` is a measure
   space and `E` is a real normed space.

  * `integral_zero`                  : `∫ 0 ∂μ = 0`
  * `integral_add`                   : `∫ x, f x + g x ∂μ = ∫ x, f ∂μ + ∫ x, g x ∂μ`
  * `integral_neg`                   : `∫ x, - f x ∂μ = - ∫ x, f x ∂μ`
  * `integral_sub`                   : `∫ x, f x - g x ∂μ = ∫ x, f x ∂μ - ∫ x, g x ∂μ`
  * `integral_smul`                  : `∫ x, r • f x ∂μ = r • ∫ x, f x ∂μ`
  * `integral_congr_ae`              : `f =ᵐ[μ] g → ∫ x, f x ∂μ = ∫ x, g x ∂μ`
  * `norm_integral_le_integral_norm` : `‖∫ x, f x ∂μ‖ ≤ ∫ x, ‖f x‖ ∂μ`

2. Basic order properties of the Bochner integral on functions of type `α → E`, where `α` is a
   measure space and `E` is a real ordered Banach space.

  * `integral_nonneg_of_ae` : `0 ≤ᵐ[μ] f → 0 ≤ ∫ x, f x ∂μ`
  * `integral_nonpos_of_ae` : `f ≤ᵐ[μ] 0 → ∫ x, f x ∂μ ≤ 0`
  * `integral_mono_ae`      : `f ≤ᵐ[μ] g → ∫ x, f x ∂μ ≤ ∫ x, g x ∂μ`
  * `integral_nonneg`       : `0 ≤ f → 0 ≤ ∫ x, f x ∂μ`
  * `integral_nonpos`       : `f ≤ 0 → ∫ x, f x ∂μ ≤ 0`
  * `integral_mono`         : `f ≤ᵐ[μ] g → ∫ x, f x ∂μ ≤ ∫ x, g x ∂μ`

3. Propositions connecting the Bochner integral with the integral on `ℝ≥0∞`-valued functions,
   which is called `lintegral` and has the notation `∫⁻`.

  * `integral_eq_lintegral_pos_part_sub_lintegral_neg_part` :
    `∫ x, f x ∂μ = ∫⁻ x, f⁺ x ∂μ - ∫⁻ x, f⁻ x ∂μ`,
    where `f⁺` is the positive part of `f` and `f⁻` is the negative part of `f`.
  * `integral_eq_lintegral_of_nonneg_ae`          : `0 ≤ᵐ[μ] f → ∫ x, f x ∂μ = ∫⁻ x, f x ∂μ`

4. (In the file `Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`)
  `tendsto_integral_of_dominated_convergence` : the Lebesgue dominated convergence theorem

5. (In `Mathlib/MeasureTheory/Integral/Bochner/Set.lean`) integration commutes with continuous
  linear maps.

  * `ContinuousLinearMap.integral_comp_comm`
  * `LinearIsometry.integral_comp_comm`

## Notes

Some tips on how to prove a proposition if the API for the Bochner integral is not enough so that
you need to unfold the definition of the Bochner integral and go back to simple functions.

One method is to use the theorem `Integrable.induction` in the file
`Mathlib/MeasureTheory/Function/SimpleFuncDenseLp.lean` (or one of the related results, like
`Lp.induction` for functions in `Lp`), which allows you to prove something for an arbitrary
integrable function.

Another method is using the following steps.
See `integral_eq_lintegral_pos_part_sub_lintegral_neg_part` for a complicated example, which proves
that `∫ f = ∫⁻ f⁺ - ∫⁻ f⁻`, with the first integral sign being the Bochner integral of a real-valued
function `f : α → ℝ`, and the second and third integral signs being integrals on `ℝ≥0∞`-valued
functions (called `lintegral`). The proof of `integral_eq_lintegral_pos_part_sub_lintegral_neg_part`
is scattered in sections with the name `posPart`.

Here are the usual steps of proving that a property `p`, say `∫ f = ∫⁻ f⁺ - ∫⁻ f⁻`, holds for all
functions :

1. First go to the `L¹` space.

   For example, if you see `ENNReal.toReal (∫⁻ a, ENNReal.ofReal <| ‖f a‖)`, that is the norm of
   `f` in `L¹` space. Rewrite using `L1.norm_of_fun_eq_lintegral_norm`.

2. Show that the set `{f ∈ L¹ | ∫ f = ∫⁻ f⁺ - ∫⁻ f⁻}` is closed in `L¹` using `isClosed_eq`.

3. Show that the property holds for all simple functions `s` in `L¹` space.

   Typically, you need to convert various notions to their `SimpleFunc` counterpart, using lemmas
   like `L1.integral_coe_eq_integral`.

4. Since simple functions are dense in `L¹`,
   ```
   univ = closure {s simple}
        = closure {s simple | ∫ s = ∫⁻ s⁺ - ∫⁻ s⁻} : the property holds for all simple functions
        ⊆ closure {f | ∫ f = ∫⁻ f⁺ - ∫⁻ f⁻}
        = {f | ∫ f = ∫⁻ f⁺ - ∫⁻ f⁻} : closure of a closed set is itself
   ```
   Use `isClosed_property` or `DenseRange.induction_on` for this argument.

## Notation

* `α →ₛ E` : simple functions (defined in `Mathlib/MeasureTheory/Function/SimpleFunc.lean`)
* `α →₁[μ] E` : functions in L1 space, i.e., equivalence classes of integrable functions (defined in
  `Mathlib/MeasureTheory/Function/LpSpace/Basic.lean`)
* `∫ a, f a ∂μ` : integral of `f` with respect to a measure `μ`
* `∫ a, f a` : integral of `f` with respect to `volume`, the default measure on the ambient type

We also define notations for integral on a set, which are described in the file
`Mathlib/MeasureTheory/Integral/Bochner/Set.lean`.

Note : `ₛ` is typed using `\_s`. Sometimes it shows as a box if the font is missing.

## Tags

Bochner integral, simple function, function space, Lebesgue dominated convergence theorem

-/

noncomputable section

open Filter ENNReal EMetric Set TopologicalSpace Topology

open scoped NNReal ENNReal MeasureTheory

namespace MeasureTheory

variable {α E F 𝕜 : Type*}

local infixr:25 " →ₛ " => SimpleFunc

/-!
## The Bochner integral on functions

Define the Bochner integral on functions generally to be the `L1` Bochner integral, for integrable
functions, and 0 otherwise; prove its basic properties.
-/

variable [NormedAddCommGroup E] [NormedDivisionRing 𝕜]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

open Classical in

irreducible_def integral {_ : MeasurableSpace α} (μ : Measure α) (f : α → G) : G :=
  if _ : CompleteSpace G then
    if hf : Integrable f μ then L1.integral (hf.toL1 f) else 0
  else 0

/-! In the notation for integrals, an expression like `∫ x, g ‖x‖ ∂μ` will not be parsed correctly,
  and needs parentheses. We do not set the binding power of `r` to `0`, because then
  `∫ x, f x = 0` will be parsed incorrectly. -/
