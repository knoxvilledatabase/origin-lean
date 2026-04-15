/-
Extracted from MeasureTheory/OuterMeasure/Defs.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Definitions of an outer measure and the corresponding `FunLike` class

In this file we define `MeasureTheory.OuterMeasure α`
to be the type of outer measures on `α`.

An outer measure is a function `μ : Set α → ℝ≥0∞`,
from the powerset of a type to the extended nonnegative real numbers
that satisfies the following conditions:
1. `μ ∅ = 0`;
2. `μ` is monotone;
3. `μ` is countably subadditive. This means that the outer measure of a countable union
   is at most the sum of the outer measure on the individual sets.

Note that we do not need `α` to be measurable to define an outer measure.

We also define a typeclass `MeasureTheory.OuterMeasureClass`.

## References

<https://en.wikipedia.org/wiki/Outer_measure>

## Tags

outer measure
-/

assert_not_exists Module.Basis IsTopologicalRing UniformSpace

open scoped ENNReal

variable {α : Type*}

namespace MeasureTheory

open scoped Function -- required for scoped `on` notation

structure OuterMeasure (α : Type*) where
  /-- Outer measure function. Use automatic coercion instead. -/
  protected measureOf : Set α → ℝ≥0∞
  protected empty : measureOf ∅ = 0
  protected mono : ∀ {s₁ s₂}, s₁ ⊆ s₂ → measureOf s₁ ≤ measureOf s₂
  protected iUnion_nat : ∀ s : ℕ → Set α, Pairwise (Disjoint on s) →
    measureOf (⋃ i, s i) ≤ ∑' i, measureOf (s i)

class OuterMeasureClass (F : Type*) (α : outParam Type*) [FunLike F (Set α) ℝ≥0∞] : Prop where
  protected measure_empty (f : F) : f ∅ = 0
  protected measure_mono (f : F) {s t} : s ⊆ t → f s ≤ f t
  protected measure_iUnion_nat_le (f : F) (s : ℕ → Set α) : Pairwise (Disjoint on s) →
    f (⋃ i, s i) ≤ ∑' i, f (s i)

namespace OuterMeasure

-- INSTANCE (free from Core): :
