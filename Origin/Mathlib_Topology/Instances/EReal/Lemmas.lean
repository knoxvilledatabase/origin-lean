/-
Extracted from Topology/Instances/EReal/Lemmas.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Topological structure on `EReal`

We prove basic properties of the topology on `EReal`.

## Main results

* `Real.toEReal : ℝ → EReal` is an open embedding
* `ENNReal.toEReal : ℝ≥0∞ → EReal` is a closed embedding
* The addition on `EReal` is continuous except at `(⊥, ⊤)` and at `(⊤, ⊥)`.
* Negation is a homeomorphism on `EReal`.

## Implementation

Most proofs are adapted from the corresponding proofs on `ℝ≥0∞`.
-/

noncomputable section

open Set Filter Metric TopologicalSpace Topology

open scoped ENNReal

variable {α : Type*} [TopologicalSpace α]

namespace EReal

/-! ### Real coercion -/

theorem isEmbedding_coe : IsEmbedding ((↑) : ℝ → EReal) :=
  coe_strictMono.isEmbedding_of_ordConnected <| by rw [range_coe_eq_Ioo]; exact ordConnected_Ioo

theorem isOpenEmbedding_coe : IsOpenEmbedding ((↑) : ℝ → EReal) :=
  ⟨isEmbedding_coe, by simp only [range_coe_eq_Ioo, isOpen_Ioo]⟩
