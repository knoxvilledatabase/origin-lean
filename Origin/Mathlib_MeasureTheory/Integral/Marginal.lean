/-
Extracted from MeasureTheory/Integral/Marginal.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Marginals of multivariate functions

In this file, we define a convenient way to compute integrals of multivariate functions, especially
if you want to write expressions where you integrate only over some of the variables that the
function depends on. This is common in induction arguments involving integrals of multivariate
functions.
This constructions allows working with iterated integrals and applying Tonelli's theorem
and Fubini's theorem, without using measurable equivalences by changing the representation of your
space (e.g. `((ι ⊕ ι') → ℝ) ≃ (ι → ℝ) × (ι' → ℝ)`).

## Main Definitions

* Assume that `∀ i : ι, X i` is a product of measurable spaces with measures `μ i` on `X i`,
  `f : (∀ i, X i) → ℝ≥0∞` is a function and `s : Finset ι`.
  Then `lmarginal μ s f` or `∫⋯∫⁻_s, f ∂μ` is the function that integrates `f`
  over all variables in `s`. It returns a function that still takes the same variables as `f`,
  but is constant in the variables in `s`. Mathematically, if `s = {i₁, ..., iₖ}`,
  then `lmarginal μ s f` is the expression
  $$
  \vec{x}\mapsto \int\!\!\cdots\!\!\int f(\vec{x}[\vec{y}])dy_{i_1}\cdots dy_{i_k}.
  $$
  where $\vec{x}[\vec{y}]$ is the vector $\vec{x}$ with $x_{i_j}$ replaced by $y_{i_j}$ for all
  $1 \le j \le k$.
  If `f` is the distribution of a random variable, this is the marginal distribution of all
  variables not in `s` (but not the most general notion, since we only consider product measures
  here).
  Note that the notation `∫⋯∫⁻_s, f ∂μ` is not a binder, and returns a function.

## Main Results

* `lmarginal_union` is the analogue of Tonelli's theorem for iterated integrals. It states that
  for measurable functions `f` and disjoint finsets `s` and `t` we have
  `∫⋯∫⁻_s ∪ t, f ∂μ = ∫⋯∫⁻_s, ∫⋯∫⁻_t, f ∂μ ∂μ`.

## Implementation notes

The function `f` can have an arbitrary product as its domain (even infinite products), but the
set `s` of integration variables is a `Finset`. We are assuming that the function `f` is measurable
for most of this file. Note that asking whether it is `AEMeasurable` is not even well-posed,
since there is no well-behaved measure on the domain of `f`.

## TODO

* Define the marginal function for functions taking values in a Banach space.

-/

open scoped ENNReal

open Set Function Equiv Finset

noncomputable section

namespace MeasureTheory

section LMarginal

variable {δ δ' : Type*} {X : δ → Type*} [∀ i, MeasurableSpace (X i)]

variable {μ : ∀ i, Measure (X i)} [DecidableEq δ]

variable {s t : Finset δ} {f : (∀ i, X i) → ℝ≥0∞} {x : ∀ i, X i}

def lmarginal (μ : ∀ i, Measure (X i)) (s : Finset δ) (f : (∀ i, X i) → ℝ≥0∞)
    (x : ∀ i, X i) : ℝ≥0∞ :=
  ∫⁻ y : ∀ i : s, X i, f (updateFinset x s y) ∂Measure.pi fun i : s => μ i
