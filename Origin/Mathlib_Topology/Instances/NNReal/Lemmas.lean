/-
Extracted from Topology/Instances/NNReal/Lemmas.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Topology on `ℝ≥0`

The basic lemmas for the natural topology on `ℝ≥0` .

## Main statements

Various mathematically trivial lemmas are proved about the compatibility
of limits and sums in `ℝ≥0` and `ℝ`. For example

* `tendsto_coe {f : Filter α} {m : α → ℝ≥0} {x : ℝ≥0} :
  Filter.Tendsto (fun a, (m a : ℝ)) f (𝓝 (x : ℝ)) ↔ Filter.Tendsto m f (𝓝 x)`

says that the limit of a filter along a map to `ℝ≥0` is the same in `ℝ` and `ℝ≥0`, and

* `coe_tsum {f : α → ℝ≥0} : ((∑'a, f a) : ℝ) = (∑'a, (f a : ℝ))`

says that says that a sum of elements in `ℝ≥0` is the same in `ℝ` and `ℝ≥0`.

Similarly, some mathematically trivial lemmas about infinite sums are proved,
a few of which rely on the fact that subtraction is continuous.

-/

noncomputable section

open Filter Metric Set TopologicalSpace Topology

variable {ι : Sort*} {n : ℕ}

namespace NNReal

variable {α : Type*} {L : SummationFilter α}

section coe

lemma isOpen_Ico_zero {x : NNReal} : IsOpen (Set.Ico 0 x) :=
  Ico_bot (a := x) ▸ isOpen_Iio

open Filter Finset
