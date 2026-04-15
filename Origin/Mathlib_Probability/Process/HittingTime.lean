/-
Extracted from Probability/Process/HittingTime.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Hitting times

Given a stochastic process, the hitting time provides the first time the process "hits" some
subset of the state space. The hitting time is a stopping time in the case that the time index is
discrete and the process is strongly adapted (this is true in a far more general setting however
we have only proved it for the discrete case so far).

## Main definition

* `MeasureTheory.hittingBtwn u s n m`: the first time a stochastic process `u` enters a set `s`
  after time `n` and before time `m`
* `MeasureTheory.hittingAfter u s n`: the first time a stochastic process `u` enters a set `s`
  after time `n`

## Main results

* `MeasureTheory.Adapted.isStoppingTime_hittingBtwn`: a discrete hitting time of an adapted process
  is a stopping time
* `MeasureTheory.Adapted.isStoppingTime_hittingAfter`: a discrete hitting time of a adapted process
  is a stopping time

-/

open Filter Order TopologicalSpace

open scoped MeasureTheory NNReal ENNReal Topology

namespace MeasureTheory

variable {Ω β ι : Type*} {m : MeasurableSpace Ω}

section Basic

variable [Preorder ι] [InfSet ι] {u : ι → Ω → β}

open scoped Classical in

noncomputable def hittingBtwn (u : ι → Ω → β)
    (s : Set β) (n m : ι) : Ω → ι :=
  fun x => if ∃ j ∈ Set.Icc n m, u j x ∈ s
    then sInf (Set.Icc n m ∩ {i : ι | u i x ∈ s}) else m
