/-
Extracted from Combinatorics/SimpleGraph/Coloring/VertexColoring.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Graph Coloring

This module defines colorings of simple graphs (also known as proper colorings in the literature).
A graph coloring is the attribution of "colors" to all of its vertices such that adjacent vertices
have different colors.
A coloring can be represented as a homomorphism into a complete graph, whose vertices represent
the colors.

## Main definitions

* `G.Coloring α` is the type of `α`-colorings of a simple graph `G`,
  with `α` being the set of available colors. The type is defined to
  be homomorphisms from `G` into the complete graph on `α`, and
  colorings have a coercion to `V → α`.

* `G.Colorable n` is the proposition that `G` is `n`-colorable, which
  is whether there exists a coloring with at most *n* colors.

* `G.chromaticNumber` is the minimal `n` such that `G` is `n`-colorable,
  or `⊤` if it cannot be colored with finitely many colors.
  (Cardinal-valued chromatic numbers are more niche, so we stick to `ℕ∞`.)
  We write `G.chromaticNumber ≠ ⊤` to mean a graph is colorable with finitely many colors.

* `C.colorClass c` is the set of vertices colored by `c : α` in the coloring `C : G.Coloring α`.

* `C.colorClasses` is the set containing all color classes.

## TODO

  * Gather material from:
    * https://github.com/leanprover-community/mathlib/blob/simple_graph_matching/src/combinatorics/simple_graph/coloring.lean
    * https://github.com/kmill/lean-graphcoloring/blob/master/src/graph.lean

  * Trees

  * Planar graphs

  * Chromatic polynomials

  * develop API for partial colorings, likely as colorings of subgraphs (`H.coe.Coloring α`)
-/

assert_not_exists Field

open Fintype Function

universe u v

namespace SimpleGraph

variable {V : Type u} (G : SimpleGraph V) {n : ℕ}

abbrev Coloring (α : Type v) := G →g completeGraph α

variable {G}

variable {ι α β : Type*} (C : G.Coloring α)

theorem Coloring.valid {v w : V} (h : G.Adj v w) : C v ≠ C w :=
  C.map_rel h

lemma Coloring.injective_comp_of_pairwise_adj (C : G.Coloring α) (f : ι → V)
    (hf : Pairwise fun i j ↦ G.Adj (f i) (f j)) : (C ∘ f).Injective :=
  Function.injective_iff_pairwise_ne.2 <| hf.mono fun _ _ ↦ C.valid
