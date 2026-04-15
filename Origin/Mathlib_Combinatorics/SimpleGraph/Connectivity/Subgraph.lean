/-
Extracted from Combinatorics/SimpleGraph/Connectivity/Subgraph.lean
Genuine: 8 of 12 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# Connectivity of subgraphs and induced graphs

## Main definitions

* `SimpleGraph.Subgraph.Preconnected` and `SimpleGraph.Subgraph.Connected` give subgraphs
  connectivity predicates via `SimpleGraph.Subgraph.coe`.

-/

namespace SimpleGraph

universe u v

variable {V : Type u} {V' : Type v} {G : SimpleGraph V} {G' : SimpleGraph V'}

namespace Subgraph

protected structure Preconnected (H : G.Subgraph) : Prop where
  protected coe : H.coe.Preconnected

-- INSTANCE (free from Core): {H

-- INSTANCE (free from Core): {H

protected lemma preconnected_iff {H : G.Subgraph} :
    H.Preconnected ↔ H.coe.Preconnected := ⟨fun ⟨h⟩ => h, .mk⟩

protected structure Connected (H : G.Subgraph) : Prop where
  protected coe : H.coe.Connected

-- INSTANCE (free from Core): {H

-- INSTANCE (free from Core): {H

protected lemma connected_iff' {H : G.Subgraph} :
    H.Connected ↔ H.coe.Connected := ⟨fun ⟨h⟩ => h, .mk⟩

protected lemma connected_iff {H : G.Subgraph} :
    H.Connected ↔ H.Preconnected ∧ H.verts.Nonempty := by
  rw [H.connected_iff', connected_iff, H.preconnected_iff, Set.nonempty_coe_sort]

protected lemma Connected.preconnected {H : G.Subgraph} (h : H.Connected) : H.Preconnected := by
  rw [H.connected_iff] at h; exact h.1

protected lemma Connected.nonempty {H : G.Subgraph} (h : H.Connected) : H.verts.Nonempty := by
  rw [H.connected_iff] at h; exact h.2

theorem singletonSubgraph_connected {v : V} : (G.singletonSubgraph v).Connected :=
  ⟨⟨Preconnected.of_subsingleton⟩⟩
