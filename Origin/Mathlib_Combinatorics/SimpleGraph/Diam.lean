/-
Extracted from Combinatorics/SimpleGraph/Diam.lean
Genuine: 6 of 9 | Dissolved: 1 | Infrastructure: 2
-/
import Origin.Core

/-!
# Diameter of a simple graph

This module defines the eccentricity of vertices, the diameter, and the radius of a simple graph.

## Main definitions

- `SimpleGraph.eccent`: the eccentricity of a vertex in a simple graph, which is the maximum
  distances between it and the other vertices.

- `SimpleGraph.ediam`: the graph extended diameter, which is the maximum eccentricity.
  It is `ℕ∞`-valued.

- `SimpleGraph.diam`: the graph diameter, an `ℕ`-valued version of `SimpleGraph.ediam`.

- `SimpleGraph.radius`: the graph radius, which is the minimum eccentricity. It is `ℕ∞`-valued.

- `SimpleGraph.center`: the set of vertices with eccentricity equal to the graph's radius.

-/

assert_not_exists Field

namespace SimpleGraph

variable {α : Type*} {G G' : SimpleGraph α}

section eccent

noncomputable def eccent (G : SimpleGraph α) (u : α) : ℕ∞ :=
  ⨆ v, G.edist u v

lemma edist_le_eccent {u v : α} : G.edist u v ≤ G.eccent u :=
  le_iSup (G.edist u) v

lemma exists_edist_eq_eccent_of_finite [Finite α] (u : α) :
    ∃ v, G.edist u v = G.eccent u :=
  have : Nonempty α := Nonempty.intro u
  exists_eq_ciSup_of_finite

lemma eccent_eq_zero_of_subsingleton [Subsingleton α] (u : α) : G.eccent u = 0 := by
  simpa [eccent, edist_eq_zero_iff] using subsingleton_iff.mp ‹_› u

-- DISSOLVED: eccent_ne_zero

lemma eccent_eq_zero_iff (u : α) : G.eccent u = 0 ↔ Subsingleton α := by
  refine ⟨fun h ↦ ?_, fun _ ↦ eccent_eq_zero_of_subsingleton u⟩
  contrapose! h
  exact eccent_ne_zero u

lemma eccent_pos_iff (u : α) : 0 < G.eccent u ↔ Nontrivial α := by
  rw [pos_iff_ne_zero, ← not_subsingleton_iff_nontrivial, ← eccent_eq_zero_iff]
