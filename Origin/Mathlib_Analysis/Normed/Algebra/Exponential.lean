/-
Extracted from Analysis/Normed/Algebra/Exponential.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Exponential in a Banach algebra

In this file, we define `NormedSpace.exp : 𝔸 → 𝔸`,
the exponential map in a topological algebra `𝔸`.

While for most interesting results we need `𝔸` to be normed algebra, we do not require this in the
definition in order to make `NormedSpace.exp` independent of a particular choice of norm. The
definition also does not require that `𝔸` be complete, but we need to assume it for most results.

We then prove some basic results, but we avoid importing derivatives here to minimize dependencies.
Results involving derivatives and comparisons with `Real.exp` and `Complex.exp` can be found in
`Analysis.SpecialFunctions.Exponential`.

## Main results

We prove most result for an arbitrary field `𝕂`, and then specialize to `𝕂 = ℝ` or `𝕂 = ℂ`.

### General case

- `NormedSpace.exp_add_of_commute_of_mem_ball` : if `𝕂` has characteristic zero,
  then given two commuting elements `x` and `y` in the disk of convergence, we have
  `NormedSpace.exp (x+y) = (NormedSpace.exp x) * (NormedSpace.exp y)`
- `NormedSpace.exp_add_of_mem_ball` : if `𝕂` has characteristic zero and `𝔸` is commutative,
  then given two elements `x` and `y` in the disk of convergence, we have
  `NormedSpace.exp (x+y) = (NormedSpace.exp x) * (NormedSpace.exp y)`
- `NormedSpace.exp_neg_of_mem_ball` : if `𝕂` has characteristic zero and `𝔸` is a division ring,
  then given an element `x` in the disk of convergence,
  we have `NormedSpace.exp (-x) = (NormedSpace.exp x)⁻¹`.

### `𝕂 = ℝ` or `𝕂 = ℂ`

- `expSeries_radius_eq_top` : the `FormalMultilinearSeries` defining `NormedSpace.exp`
  has infinite radius of convergence
- `NormedSpace.exp_add_of_commute` : given two commuting elements `x` and `y`, we have
  `NormedSpace.exp (x+y) = (NormedSpace.exp x) * (NormedSpace.exp y)`
- `NormedSpace.exp_add` : if `𝔸` is commutative, then we have
  `NormedSpace.exp (x+y) = (NormedSpace.exp x) * (NormedSpace.exp y)` for any `x` and `y`
- `NormedSpace.exp_neg` : if `𝔸` is a division ring, then we have
  `NormedSpace.exp (-x) = (NormedSpace.exp x)⁻¹`.
- `NormedSpace.exp_sum_of_commute` : the analogous result to `NormedSpace.exp_add_of_commute`
  for `Finset.sum`.
- `NormedSpace.exp_sum` : the analogous result to `NormedSpace.exp_add` for `Finset.sum`.
- `NormedSpace.exp_nsmul` : repeated addition in the domain corresponds to
  repeated multiplication in the codomain.
- `NormedSpace.exp_zsmul` : repeated addition in the domain corresponds to
  repeated multiplication in the codomain.

### Notes

We put nearly all the statements in this file in the `NormedSpace` namespace,
to avoid collisions with the `Real` or `Complex` namespaces.

As of 2023-11-16 due to bad instances in Mathlib
```
import Mathlib

open Real

#time example (x : ℝ) : 0 < exp x      := exp_pos _ -- 250ms
#time example (x : ℝ) : 0 < Real.exp x := exp_pos _ -- 2ms
```
This is because `exp x` tries the `NormedSpace.exp 𝕂 : 𝔸 → 𝔸` function previously defined here,
and generates a slow coercion search from `Real` to `Type`, to fit the first argument here.
We will resolve this slow coercion separately,
but we want to move `exp` out of the root namespace in any case to avoid this ambiguity.

To avoid explicitly passing the base field `𝕂`, we currently fix `𝕂 = ℚ` in the definition of
`NormedSpace.exp : 𝔸 → 𝔸`. If `𝔸` can be equipped with a `ℚ`-algebra structure, we use
`Classical.choice` to pick the unique `Algebra ℚ 𝔸` instead of requiring an instance argument.
This eliminates the need to provide `Algebra ℚ 𝔸` every time `exp` is used. If `𝔸` can't be equipped
with a `ℚ`-algebra structure, we use the junk value `1`.

In the long term it may be possible to replace `Real.exp` and `Complex.exp` with `NormedSpace.exp`
and move it back to the root namespace.
-/

namespace NormedSpace

open Filter RCLike ContinuousMultilinearMap NormedField Asymptotics FormalMultilinearSeries

open scoped Nat Topology ENNReal Ring

section TopologicalAlgebra

variable (𝕂 𝔸 : Type*) [Field 𝕂] [Ring 𝔸] [Algebra 𝕂 𝔸] [TopologicalSpace 𝔸] [IsTopologicalRing 𝔸]

def expSeries : FormalMultilinearSeries 𝕂 𝔸 𝔸 := fun n =>
  (n !⁻¹ : 𝕂) • ContinuousMultilinearMap.mkPiAlgebraFin 𝕂 n 𝔸

theorem expSeries_eq_ofScalars : expSeries 𝕂 𝔸 = ofScalars 𝔸 fun n ↦ (n !⁻¹ : 𝕂) := by
  simp_rw [FormalMultilinearSeries.ext_iff, expSeries, ofScalars, implies_true]

variable {𝕂 𝔸}

open scoped Classical in

noncomputable irreducible_def exp (x : 𝔸) : 𝔸 :=
  if h : Nonempty (Algebra ℚ 𝔸) then
    letI _ := h.some
    (NormedSpace.expSeries ℚ 𝔸).sum x
  else
    1
