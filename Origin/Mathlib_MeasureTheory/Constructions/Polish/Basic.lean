/-
Extracted from MeasureTheory/Constructions/Polish/Basic.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The Borel sigma-algebra on Polish spaces

We discuss several results pertaining to the relationship between the topology and the Borel
structure on Polish spaces.

## Main definitions and results

First, we define standard Borel spaces.

* A `StandardBorelSpace α` is a typeclass for measurable spaces which arise as the Borel sets
  of some Polish topology.

Next, we define the class of analytic sets and establish its basic properties.

* `MeasureTheory.AnalyticSet s`: a set in a topological space is analytic if it is the continuous
  image of a Polish space. Equivalently, it is empty, or the image of `ℕ → ℕ`.
* `MeasureTheory.AnalyticSet.image_of_continuous`: a continuous image of an analytic set is
  analytic.
* `MeasurableSet.analyticSet`: in a Polish space, any Borel-measurable set is analytic.

Then, we show Lusin's theorem that two disjoint analytic sets can be separated by Borel sets.

* `MeasurablySeparable s t` states that there exists a measurable set containing `s` and disjoint
  from `t`.
* `AnalyticSet.measurablySeparable` shows that two disjoint analytic sets are separated by a
  Borel set.

We then prove the Lusin-Souslin theorem that a continuous injective image of a Borel subset of
a Polish space is Borel. The proof of this nontrivial result relies on the above results on
analytic sets.

* `MeasurableSet.image_of_continuousOn_injOn` asserts that, if `s` is a Borel measurable set in
  a Polish space, then the image of `s` under a continuous injective map is still Borel measurable.
* `Continuous.measurableEmbedding` states that a continuous injective map on a Polish space
  is a measurable embedding for the Borel sigma-algebra.
* `ContinuousOn.measurableEmbedding` is the same result for a map restricted to a measurable set
  on which it is continuous.
* `Measurable.measurableEmbedding` states that a measurable injective map from
  a standard Borel space to a second-countable topological space is a measurable embedding.
* `isClopenable_iff_measurableSet`: in a Polish space, a set is clopenable (i.e., it can be made
  open and closed by using a finer Polish topology) if and only if it is Borel-measurable.

We use this to prove several versions of the Borel isomorphism theorem.

* `PolishSpace.measurableEquivOfNotCountable` : Any two uncountable standard Borel spaces
  are Borel isomorphic.
* `PolishSpace.Equiv.measurableEquiv` : Any two standard Borel spaces of the same cardinality
  are Borel isomorphic.
-/

open Set Function PolishSpace PiNat TopologicalSpace Bornology Metric Filter Topology MeasureTheory

/-! ### Standard Borel Spaces -/

variable (α : Type*)

class StandardBorelSpace [MeasurableSpace α] : Prop where
  /-- There exists a compatible Polish topology. -/
  polish : ∃ _ : TopologicalSpace α, BorelSpace α ∧ PolishSpace α

class UpgradedStandardBorel extends MeasurableSpace α, TopologicalSpace α,
  BorelSpace α, PolishSpace α
