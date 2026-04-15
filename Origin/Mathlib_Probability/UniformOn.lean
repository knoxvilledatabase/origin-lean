/-
Extracted from Probability/UniformOn.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Classical probability

The classical formulation of probability states that the probability of an event occurring in a
finite probability space is the ratio of that event to all possible events.
This notion can be expressed with measure theory using
the counting measure. In particular, given the sets `s` and `t`, we define the probability of `t`
occurring in `s` to be `|s|⁻¹ * |s ∩ t|`. With this definition, we recover the probability over
the entire sample space when `s = Set.univ`.

Classical probability is often used in combinatorics and we prove some useful lemmas in this file
for that purpose.

## Main definition

* `ProbabilityTheory.uniformOn`: given a set `s`, `uniformOn s` is the counting measure
  conditioned on `s`. This is a probability measure when `s` is finite and nonempty.

## Notes

The original aim of this file is to provide a measure-theoretic method of describing the
probability an element of a set `s` satisfies some predicate `P`. Our current formulation still
allows us to describe this by abusing the definitional equality of sets and predicates by simply
writing `uniformOn s P`. We should avoid this however as none of the lemmas are written for
predicates.
-/

noncomputable section

open ProbabilityTheory

open MeasureTheory MeasurableSpace Finset

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {s : Set Ω}

def uniformOn (s : Set Ω) : Measure Ω :=
  Measure.count[|s]

deriving IsZeroOrProbabilityMeasure
