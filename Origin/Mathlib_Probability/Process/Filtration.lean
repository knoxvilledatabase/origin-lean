/-
Extracted from Probability/Process/Filtration.lean
Genuine: 3 of 4 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Filtrations

This file defines filtrations of a measurable space and σ-finite filtrations.

## Main definitions

* `MeasureTheory.Filtration`: a filtration on a measurable space. That is, a monotone sequence of
  sub-σ-algebras.
* `MeasureTheory.SigmaFiniteFiltration`: a filtration `f` is σ-finite with respect to a measure
  `μ` if for all `i`, `μ.trim (f.le i)` is σ-finite.
* `MeasureTheory.Filtration.natural`: the smallest filtration that makes a process adapted. That
  notion `adapted` is not defined yet in this file. See `MeasureTheory.adapted`.
* `MeasureTheory.Filtration.rightCont`: the right-continuation of a filtration.
* `MeasureTheory.Filtration.IsRightContinuous`: a filtration is right-continuous if it is equal
  to its right-continuation.

## Main results

* `MeasureTheory.Filtration.instCompleteLattice`: filtrations are a complete lattice.

## Tags

filtration, stochastic process

-/

open Filter Order TopologicalSpace

open scoped MeasureTheory NNReal ENNReal Topology

namespace MeasureTheory

structure Filtration {Ω : Type*} (ι : Type*) [Preorder ι] (m : MeasurableSpace Ω) where
  /-- The sequence of sub-σ-algebras of `m` -/
  seq : ι → MeasurableSpace Ω
  mono' : Monotone seq
  le' : ∀ i : ι, seq i ≤ m

attribute [coe] Filtration.seq

variable {Ω ι : Type*} {m : MeasurableSpace Ω}

-- INSTANCE (free from Core): [Preorder

namespace Filtration

variable [Preorder ι]

protected theorem mono {i j : ι} (f : Filtration ι m) (hij : i ≤ j) : f i ≤ f j :=
  f.mono' hij

protected theorem le (f : Filtration ι m) (i : ι) : f i ≤ m :=
  f.le' i
