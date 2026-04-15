/-
Extracted from Combinatorics/SimpleGraph/Density.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Edge density

This file defines the number and density of edges of a relation/graph.

## Main declarations

Between two finsets of vertices,
* `Rel.interedges`: Finset of edges of a relation.
* `Rel.edgeDensity`: Edge density of a relation.
* `SimpleGraph.interedges`: Finset of edges of a graph.
* `SimpleGraph.edgeDensity`: Edge density of a graph.
-/

open Finset

variable {𝕜 ι κ α β : Type*}

/-! ### Density of a relation -/

namespace Rel

section Asymmetric

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  (r : α → β → Prop) [∀ a, DecidablePred (r a)] {s s₁ s₂ : Finset α}
  {t t₁ t₂ : Finset β} {a : α} {b : β} {δ : 𝕜}

def interedges (s : Finset α) (t : Finset β) : Finset (α × β) := {e ∈ s ×ˢ t | r e.1 e.2}

def edgeDensity (s : Finset α) (t : Finset β) : ℚ := #(interedges r s t) / (#s * #t)

variable {r}

theorem mem_interedges_iff {x : α × β} : x ∈ interedges r s t ↔ x.1 ∈ s ∧ x.2 ∈ t ∧ r x.1 x.2 := by
  rw [interedges, mem_filter, Finset.mem_product, and_assoc]

theorem mk_mem_interedges_iff : (a, b) ∈ interedges r s t ↔ a ∈ s ∧ b ∈ t ∧ r a b :=
  mem_interedges_iff
