/-
Extracted from Combinatorics/SimpleGraph/UnitDistance/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Unit-distance graph embeddings

An embedding of a graph into some metric space is _unit-distance_ if the distance between any two
adjacent vertices is 1. The space in question is usually the Euclidean plane, but can also be
higher-dimensional Euclidean space or the sphere (cf. [Frankl_2020]). We do not require nonadjacent
vertices to not be distance 1 apart as [hong2014] does.

## Main definitions

* `G.UnitDistEmbedding E` is a unit-distance embedding of `G` into `E`.
* `UnitDistEmbedding.copy`, `UnitDistEmbedding.embed`, `UnitDistEmbedding.iso`: transfer a
  unit-distance embedding down a `Copy`, graph embedding or graph isomorphism respectively.
-/

namespace SimpleGraph

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} {E : Type*} [MetricSpace E]

variable (G E) in

structure UnitDistEmbedding where
  /-- The embedding itself (position of vertices) -/
  p : V ↪ E
  /-- The distance between any two adjacent vertices is 1. -/
  unit_dist {u v} (ha : G.Adj u v) : dist (p u) (p v) = 1

namespace UnitDistEmbedding
