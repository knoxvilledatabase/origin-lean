/-
Extracted from Combinatorics/Graph/Basic.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Multigraphs

A multigraph is a set of vertices and a set of edges,
together with incidence data that associates each edge `e`
with an unordered pair `s(x,y)` of vertices called the *ends* of `e`.
The pair of `e` and `s(x,y)` is called a *link*.
The vertices `x` and `y` may be equal, in which case `e` is a *loop*.
There may be more than one edge with the same ends.

If a multigraph has no loops and has at most one edge for every given ends, it is called *simple*,
and these objects are also formalized as `SimpleGraph`.

This module defines `Graph α β` for a vertex type `α` and an edge type `β`,
and gives basic API for incidence, adjacency and extensionality.
The design broadly follows [Chou1994].

## Main definitions

For `G : Graph α β`, ...

* `V(G)` denotes the vertex set of `G` as a term in `Set α`.
* `E(G)` denotes the edge set of `G` as a term in `Set β`.
* `G.IsLink e x y` means that the edge `e : β` has vertices `x : α` and `y : α` as its ends.
* `G.Inc e x` means that the edge `e : β` has `x` as one of its ends.
* `G.Adj x y` means that there is an edge `e` having `x` and `y` as its ends.
* `G.IsLoopAt e x` means that `e` is a loop edge with both ends equal to `x`.
* `G.IsNonloopAt e x` means that `e` is a non-loop edge with one end equal to `x`.
* `G.incidenceSet x` is the set of edges incident to `x`.
* `G.loopSet x` is the set of loops with both ends equal to `x`.
* `G.copy` creates a definitional copy of a graph with propositionally equal data.
* `G.Compatible H` means that `G` and `H` agree on the incidence relation for their shared edges.
* `Graph.noEdge V` is the graph with vertex set `V` and no edges.
* `Graph.bouquet v E` is the graph with vertex set `{v}` and edge set `E`,
  where every edge is a loop at `v`.
* `Graph.banana u v E` is the graph with vertex set `{u, v}` and edge set `E`,
  where every edge connects `u` and `v`.

## Implementation notes

Unlike the design of `SimpleGraph`, the vertex and edge sets of `G` are modelled as sets
`V(G) : Set α` and `E(G) : Set β`, within ambient types, rather than being types themselves.
This mimics the 'embedded set' design used in `Matroid`, which seems to be more convenient for
formalizing real-world proofs in combinatorics.

A specific advantage is that this allows subgraphs of `G : Graph α β` to also exist on
an equal footing with `G` as terms in `Graph α β`,
and so there is no need for a `Graph.subgraph` type and all the associated
definitions and canonical coercion maps. The same will go for minors and the various other
partial orders on multigraphs.

The main tradeoff is that parts of the API will need to care about whether a term
`x : α` or `e : β` is a 'real' vertex or edge of the graph, rather than something outside
the vertex or edge set. This is an issue, but is likely amenable to automation.

## Notation

Reflecting written mathematics, we use the compact notations `V(G)` and `E(G)` to
refer to the `vertexSet` and `edgeSet` of `G : Graph α β`.
If `G.IsLink e x y` then we refer to `e` as `edge` and `x` and `y` as `left` and `right` in names.
-/

variable {α β : Type*} {x y z u v w : α} {e f : β}

open Set

structure Graph (α β : Type*) where
  /-- The vertex set. -/
  vertexSet : Set α
  /-- The binary incidence predicate, stating that `x` and `y` are the ends of an edge `e`.
  If `G.IsLink e x y` then we refer to `e` as `edge` and `x` and `y` as `left` and `right`. -/
  IsLink : β → α → α → Prop
  /-- The edge set. -/
  edgeSet : Set β := {e | ∃ x y, IsLink e x y}
  /-- If `e` goes from `x` to `y`, it goes from `y` to `x`. -/
  isLink_symm : ∀ ⦃e⦄, e ∈ edgeSet → (Symmetric <| IsLink e)
  /-- An edge is incident with at most one pair of vertices. -/
  eq_or_eq_of_isLink_of_isLink : ∀ ⦃e x y v w⦄, IsLink e x y → IsLink e v w → x = v ∨ x = w
  /-- An edge `e` is incident to something if and only if `e` is in the edge set. -/
  edge_mem_iff_exists_isLink : ∀ e, e ∈ edgeSet ↔ ∃ x y, IsLink e x y := by exact fun _ ↦ Iff.rfl
  /-- If some edge `e` is incident to `x`, then `x ∈ V`. -/
  left_mem_of_isLink : ∀ ⦃e x y⦄, IsLink e x y → x ∈ vertexSet

initialize_simps_projections Graph (IsLink → isLink)

namespace Graph

variable {G H : Graph α β}

scoped notation "V(" G ")" => Graph.vertexSet G

scoped notation "E(" G ")" => Graph.edgeSet G

/-! ### Edge-vertex-vertex incidence -/

lemma IsLink.edge_mem (h : G.IsLink e x y) : e ∈ E(G) :=
  (edge_mem_iff_exists_isLink ..).2 ⟨x, y, h⟩
