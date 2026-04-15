/-
Extracted from Probability/Process/Adapted.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Adapted and progressively measurable processes

This file defines the related notions of a process `u` being `Adapted`, `StronglyAdapted`
or `ProgMeasurable` (progressively measurable) with respect to a filter `f`, and proves
some basic facts about them.

## Main definitions

* `MeasureTheory.Adapted`: a sequence of functions `u` is said to be adapted to a
  filtration `f` if at each point in time `i`, `u i` is `f i`-measurable
* `MeasureTheory.StronglyAdapted`: a sequence of functions `u` is said to be strongly adapted to a
  filtration `f` if at each point in time `i`, `u i` is `f i`-strongly measurable
* `MeasureTheory.ProgMeasurable`: a sequence of functions `u` is said to be progressively
  measurable with respect to a filtration `f` if at each point in time `i`, `u` restricted to
  `Set.Iic i × Ω` is strongly measurable with respect to the product `MeasurableSpace` structure
  where the σ-algebra used for `Ω` is `f i`.

## Main results

* `StronglyAdapted.progMeasurable_of_continuous`: a continuous strongly adapted process is
  progressively measurable.

## Tags

adapted, progressively measurable

-/

open Filter Order TopologicalSpace

open scoped MeasureTheory NNReal ENNReal Topology

namespace MeasureTheory

variable {Ω ι : Type*} {m : MeasurableSpace Ω} [Preorder ι] {f : Filtration ι m}

section Adapted

variable {β : ι → Type*} [∀ i, MeasurableSpace (β i)] {u v : (i : ι) → Ω → β i}

def Adapted (f : Filtration ι m) (u : (i : ι) → Ω → β i) : Prop :=
  ∀ i : ι, Measurable[f i] (u i)

namespace Adapted
