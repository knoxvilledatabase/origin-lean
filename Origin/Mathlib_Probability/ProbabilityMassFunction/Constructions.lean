/-
Extracted from Probability/ProbabilityMassFunction/Constructions.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Specific Constructions of Probability Mass Functions

This file gives a number of different `PMF` constructions for common probability distributions.

`map` and `seq` allow pushing a `PMF α` along a function `f : α → β` (or distribution of
functions `f : PMF (α → β)`) to get a `PMF β`.

`ofFinset` and `ofFintype` simplify the construction of a `PMF α` from a function `f : α → ℝ≥0∞`,
by allowing the "sum equals 1" constraint to be in terms of `Finset.sum` instead of `tsum`.

`normalize` constructs a `PMF α` by normalizing a function `f : α → ℝ≥0∞` by its sum,
and `filter` uses this to filter the support of a `PMF` and re-normalize the new distribution.

`bernoulli` represents the Bernoulli distribution on `Bool`.

-/

universe u v

namespace PMF

noncomputable section

variable {α β γ : Type*}

open NNReal ENNReal Finset MeasureTheory

section Map

def map (f : α → β) (p : PMF α) : PMF β :=
  bind p (pure ∘ f)

variable (f : α → β) (p : PMF α) (b : β)

open scoped Classical in
