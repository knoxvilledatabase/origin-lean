/-
Extracted from Combinatorics/SimpleGraph/Extremal/Turan.lean
Genuine: 3 of 4 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Turán's theorem

In this file we prove Turán's theorem, the first important result of extremal graph theory,
which states that the `r + 1`-cliquefree graph on `n` vertices with the most edges is the complete
`r`-partite graph with part sizes as equal as possible (`turanGraph n r`).

The forward direction of the proof performs "Zykov symmetrisation", which first shows
constructively that non-adjacency is an equivalence relation in a maximal graph, so it must be
complete multipartite with the parts being the equivalence classes. Then basic manipulations
show that the graph is isomorphic to the Turán graph for the given parameters.

For the reverse direction we first show that a Turán-maximal graph exists, then transfer
the property through `turanGraph n r` using the isomorphism provided by the forward direction.

## Main declarations

* `SimpleGraph.IsTuranMaximal`: `G.IsTuranMaximal r` means that `G` has the most number of edges for
  its number of vertices while still being `r + 1`-cliquefree.
* `SimpleGraph.turanGraph n r`: The canonical `r + 1`-cliquefree Turán graph on `n` vertices.
* `SimpleGraph.IsTuranMaximal.finpartition`: The result of Zykov symmetrisation, a finpartition of
  the vertices such that two vertices are in the same part iff they are non-adjacent.
* `SimpleGraph.IsTuranMaximal.nonempty_iso_turanGraph`: The forward direction, an isomorphism
  between `G` satisfying `G.IsTuranMaximal r` and `turanGraph n r`.
* `isTuranMaximal_of_iso`: the reverse direction, `G.IsTuranMaximal r` given the isomorphism.
* `isTuranMaximal_iff_nonempty_iso_turanGraph`: Turán's theorem in full.

## References

* https://en.wikipedia.org/wiki/Turán%27s_theorem
-/

open Finset Fintype

namespace SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj] {n r : ℕ}

variable (G) in

def IsTuranMaximal (r : ℕ) : Prop := G.IsExtremal (CliqueFree · (r + 1))

section Defs

variable {H : SimpleGraph V}

def turanGraph (n r : ℕ) : SimpleGraph (Fin n) where Adj v w := v % r ≠ w % r

lemma turanGraph_adj {v w} : (turanGraph n r).Adj v w ↔ v % r ≠ w % r :=
  .rfl

-- INSTANCE (free from Core): :
