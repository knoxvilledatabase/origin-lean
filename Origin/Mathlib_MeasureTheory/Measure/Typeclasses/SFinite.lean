/-
Extracted from MeasureTheory/Measure/Typeclasses/SFinite.lean
Genuine: 3 of 6 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Classes for s-finite measures

We introduce the following typeclasses for measures:

* `SFinite μ`: the measure `μ` can be written as a countable sum of finite measures;
* `SigmaFinite μ`: there exists a countable collection of sets that cover `univ`
  where `μ` is finite.
-/

namespace MeasureTheory

open Set Filter Function Measure MeasurableSpace NNReal ENNReal

open scoped Topology

variable {α β ι : Type*} {m0 : MeasurableSpace α} [MeasurableSpace β] {μ ν : Measure α}
  {s t : Set α} {a : α}

section SFinite

class SFinite (μ : Measure α) : Prop where
  out' : ∃ m : ℕ → Measure α, (∀ n, IsFiniteMeasure (m n)) ∧ μ = Measure.sum m

noncomputable def sfiniteSeq (μ : Measure α) [h : SFinite μ] : ℕ → Measure α := h.1.choose

-- INSTANCE (free from Core): isFiniteMeasure_sfiniteSeq

lemma sfiniteSeq_le (μ : Measure α) [SFinite μ] (n : ℕ) : sfiniteSeq μ n ≤ μ :=
  (le_sum _ n).trans (sum_sfiniteSeq μ).le

-- INSTANCE (free from Core): :
