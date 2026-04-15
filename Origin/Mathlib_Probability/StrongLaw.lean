/-
Extracted from Probability/StrongLaw.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The strong law of large numbers

We prove the strong law of large numbers, in `ProbabilityTheory.strong_law_ae`:
If `X n` is a sequence of independent identically distributed integrable random
variables, then `∑ i ∈ range n, X i / n` converges almost surely to `𝔼[X 0]`.
We give here the strong version, due to Etemadi, that only requires pairwise independence.

This file also contains the Lᵖ version of the strong law of large numbers provided by
`ProbabilityTheory.strong_law_Lp` which shows `∑ i ∈ range n, X i / n` converges in Lᵖ to
`𝔼[X 0]` provided `X n` is independent identically distributed and is Lᵖ.

## Implementation

The main point is to prove the result for real-valued random variables, as the general case
of Banach-space-valued random variables follows from this case and approximation by simple
functions. The real version is given in `ProbabilityTheory.strong_law_ae_real`.

We follow the proof by Etemadi
[Etemadi, *An elementary proof of the strong law of large numbers*][etemadi_strong_law],
which goes as follows.

It suffices to prove the result for nonnegative `X`, as one can prove the general result by
splitting a general `X` into its positive part and negative part.
Consider `Xₙ` a sequence of nonnegative integrable identically distributed pairwise independent
random variables. Let `Yₙ` be the truncation of `Xₙ` up to `n`. We claim that
* Almost surely, `Xₙ = Yₙ` for all but finitely many indices. Indeed, `∑ ℙ (Xₙ ≠ Yₙ)` is bounded by
  `1 + 𝔼[X]` (see `sum_prob_mem_Ioc_le` and `tsum_prob_mem_Ioi_lt_top`).
* Let `c > 1`. Along the sequence `n = c ^ k`, then `(∑_{i=0}^{n-1} Yᵢ - 𝔼[Yᵢ])/n` converges almost
  surely to `0`. This follows from a variance control, as
```
  ∑_k ℙ (|∑_{i=0}^{c^k - 1} Yᵢ - 𝔼[Yᵢ]| > c^k ε)
    ≤ ∑_k (c^k ε)^{-2} ∑_{i=0}^{c^k - 1} Var[Yᵢ]    (by Markov inequality)
    ≤ ∑_i (C/i^2) Var[Yᵢ]                           (as ∑_{c^k > i} 1/(c^k)^2 ≤ C/i^2)
    ≤ ∑_i (C/i^2) 𝔼[Yᵢ^2]
    ≤ 2C 𝔼[X^2]                                     (see `sum_variance_truncation_le`)
```
* As `𝔼[Yᵢ]` converges to `𝔼[X]`, it follows from the two previous items and Cesàro that, along
  the sequence `n = c^k`, one has `(∑_{i=0}^{n-1} Xᵢ) / n → 𝔼[X]` almost surely.
* To generalize it to all indices, we use the fact that `∑_{i=0}^{n-1} Xᵢ` is nondecreasing and
  that, if `c` is close enough to `1`, the gap between `c^k` and `c^(k+1)` is small.
-/

noncomputable section

open MeasureTheory Filter Finset Asymptotics

open Set (indicator)

open scoped Topology MeasureTheory ProbabilityTheory ENNReal NNReal

open scoped Function -- required for scoped `on` notation

namespace ProbabilityTheory

/-! ### Prerequisites on truncations -/

section Truncation

variable {α : Type*}

def truncation (f : α → ℝ) (A : ℝ) :=
  indicator (Set.Ioc (-A) A) id ∘ f

variable {m : MeasurableSpace α} {μ : Measure α} {f : α → ℝ}

theorem _root_.MeasureTheory.AEStronglyMeasurable.truncation (hf : AEStronglyMeasurable f μ)
    {A : ℝ} : AEStronglyMeasurable (truncation f A) μ := by
  apply AEStronglyMeasurable.comp_aemeasurable _ hf.aemeasurable
  exact (stronglyMeasurable_id.indicator measurableSet_Ioc).aestronglyMeasurable

theorem abs_truncation_le_bound (f : α → ℝ) (A : ℝ) (x : α) : |truncation f A x| ≤ |A| := by
  simp only [truncation, Set.indicator, id, Function.comp_apply]
  split_ifs with h
  · exact abs_le_abs h.2 (neg_le.2 h.1.le)
  · simp [abs_nonneg]
