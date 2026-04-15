/-
Extracted from Probability/Martingale/BorelCantelli.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Generalized Borel-Cantelli lemma

This file proves Lévy's generalized Borel-Cantelli lemma which is a generalization of the
Borel-Cantelli lemmas. With this generalization, one can easily deduce the Borel-Cantelli lemmas
by choosing appropriate filtrations. This file also contains the one-sided martingale bound which
is required to prove the generalized Borel-Cantelli.

**Note**: the usual Borel-Cantelli lemmas are not in this file.
See `MeasureTheory.measure_limsup_atTop_eq_zero` for the first (which does not depend on
the results here), and `ProbabilityTheory.measure_limsup_eq_one` for the second (which does).

## Main results

- `MeasureTheory.Submartingale.bddAbove_iff_exists_tendsto`: the one-sided martingale bound: given
  a submartingale `f` with uniformly bounded differences, the set for which `f` converges is almost
  everywhere equal to the set for which it is bounded.
- `MeasureTheory.ae_mem_limsup_atTop_iff`: Lévy's generalized Borel-Cantelli:
  given a filtration `ℱ` and a sequence of sets `s` such that `s n ∈ ℱ n` for all `n`,
  `limsup atTop s` is almost everywhere equal to the set for which `∑ ℙ[s (n + 1)∣ℱ n] = ∞`.

-/

open Filter

open scoped NNReal ENNReal MeasureTheory ProbabilityTheory Topology

namespace MeasureTheory

variable {ι Ω β : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-!
### One-sided martingale bound
-/

noncomputable def leastGE [Preorder ι] [OrderBot ι] [InfSet ι] [Preorder β]
    (f : ι → Ω → β) (r : β) : Ω → WithTop ι :=
  hittingAfter f (Set.Ici r) ⊥

theorem StronglyAdapted.isStoppingTime_leastGE [ConditionallyCompleteLinearOrderBot ι]
    {ℱ : Filtration ι m0} [WellFoundedLT ι] [Countable ι] [TopologicalSpace β]
    [Preorder β] [ClosedIciTopology β] [TopologicalSpace.PseudoMetrizableSpace β]
    [MeasurableSpace β] [BorelSpace β]
    {f : ι → Ω → β} (r : β) (hf : StronglyAdapted ℱ f) :
    IsStoppingTime ℱ (leastGE f r) :=
  hf.adapted.isStoppingTime_hittingAfter measurableSet_Ici

noncomputable def stoppedAbove [LinearOrder ι] [OrderBot ι] [InfSet ι] [Preorder β]
    (f : ι → Ω → β) (r : β) : ι → Ω → β :=
  stoppedProcess f (leastGE f r)

variable {ℱ : Filtration ℕ m0} {f : ℕ → Ω → ℝ}

protected lemma Submartingale.stoppedAbove [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ) (r : ℝ) :
    Submartingale (stoppedAbove f r) ℱ μ :=
  hf.stoppedProcess (hf.stronglyAdapted.isStoppingTime_leastGE r)
