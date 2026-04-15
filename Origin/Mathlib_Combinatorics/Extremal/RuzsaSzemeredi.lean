/-
Extracted from Combinatorics/Extremal/RuzsaSzemeredi.lean
Genuine: 7 of 7 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The Ruzsa-Szemerédi problem

This file proves the lower bound of the Ruzsa-Szemerédi problem. The problem is to find the maximum
number of edges that a graph on `n` vertices can have if all edges belong to at most one triangle.

The lower bound comes from turning the big 3AP-free set from Behrend's construction into a graph
that has the property that every triangle gives a (possibly trivial) arithmetic progression on the
original set.

## Main declarations

* `ruzsaSzemerediNumberNat n`: Maximum number of edges a graph on `n` vertices can have such that
  each edge belongs to exactly one triangle.
* `ruzsaSzemerediNumberNat_asymptotic_lower_bound`: There exists a graph with `n` vertices and
  `Ω((n ^ 2 * exp (-4 * √(log n))))` edges such that each edge belongs to exactly one triangle.
-/

open Finset Nat Real SimpleGraph Sum3 SimpleGraph.TripartiteFromTriangles

open Fintype (card)

open scoped Pointwise

variable {α β : Type*}

/-! ### The Ruzsa-Szemerédi number -/

section ruzsaSzemerediNumber

variable [DecidableEq α] [DecidableEq β] [Fintype α] [Fintype β] {G H : SimpleGraph α}

variable (α) in

noncomputable def ruzsaSzemerediNumber : ℕ := by
  classical
  exact Nat.findGreatest (fun m ↦ ∃ (G : SimpleGraph α) (_ : DecidableRel G.Adj),
    #(G.cliqueFinset 3) = m ∧ G.LocallyLinear) ((card α).choose 3)

open scoped Classical in

lemma ruzsaSzemerediNumber_le : ruzsaSzemerediNumber α ≤ (card α).choose 3 := Nat.findGreatest_le _

lemma ruzsaSzemerediNumber_spec :
    ∃ (G : SimpleGraph α) (_ : DecidableRel G.Adj),
      #(G.cliqueFinset 3) = ruzsaSzemerediNumber α ∧ G.LocallyLinear := by
  classical
  exact @Nat.findGreatest_spec _
    (fun m ↦ ∃ (G : SimpleGraph α) (_ : DecidableRel G.Adj),
      #(G.cliqueFinset 3) = m ∧ G.LocallyLinear) _ _ (Nat.zero_le _)
    ⟨⊥, inferInstance, by simp, locallyLinear_bot⟩

variable {m n : ℕ}

lemma SimpleGraph.LocallyLinear.le_ruzsaSzemerediNumber [DecidableRel G.Adj]
    (hG : G.LocallyLinear) : #(G.cliqueFinset 3) ≤ ruzsaSzemerediNumber α := by
  classical
  exact le_findGreatest card_cliqueFinset_le ⟨G, inferInstance, by congr, hG⟩

lemma ruzsaSzemerediNumber_mono (f : α ↪ β) : ruzsaSzemerediNumber α ≤ ruzsaSzemerediNumber β := by
  classical
  refine findGreatest_mono ?_ (choose_mono _ <| Fintype.card_le_of_embedding f)
  rintro n ⟨G, _, rfl, hG⟩
  refine ⟨G.map f, inferInstance, ?_, hG.map _⟩
  rw [← card_map ⟨map f, Finset.map_injective _⟩, ← cliqueFinset_map G f]
  decide

lemma ruzsaSzemerediNumber_congr (e : α ≃ β) : ruzsaSzemerediNumber α = ruzsaSzemerediNumber β :=
  (ruzsaSzemerediNumber_mono (e : α ↪ β)).antisymm <| ruzsaSzemerediNumber_mono e.symm

noncomputable def ruzsaSzemerediNumberNat (n : ℕ) : ℕ := ruzsaSzemerediNumber (Fin n)
