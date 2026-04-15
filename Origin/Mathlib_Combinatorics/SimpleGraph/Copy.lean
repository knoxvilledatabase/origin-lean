/-
Extracted from Combinatorics/SimpleGraph/Copy.lean
Genuine: 5 of 6 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Containment of graphs

This file introduces the concept of one simple graph containing a copy of another.

For two simple graphs `G` and `H`, a *copy* of `G` in `H` is a (not necessarily induced) subgraph of
`H` isomorphic to `G`.

If there exists a copy of `G` in `H`, we say that `H` *contains* `G`. This is equivalent to saying
that there is an injective graph homomorphism `G → H` between them (this is **not** the same as a
graph embedding, as we do not require the subgraph to be induced).

If there exists an induced copy of `G` in `H`, we say that `H` *inducingly contains* `G`. This is
equivalent to saying that there is a graph embedding `G ↪ H`.

## Main declarations

Containment:
* `SimpleGraph.Copy G H` is the type of copies of `G` in `H`, implemented as the subtype of
  *injective* homomorphisms.
* `SimpleGraph.IsContained G H`, `G ⊑ H` is the relation that `H` contains a copy of `G`, that
  is, the type of copies of `G` in `H` is nonempty. This is equivalent to the existence of an
  isomorphism from `G` to a subgraph of `H`.
  This is similar to `SimpleGraph.IsSubgraph` except that the simple graphs here need not have the
  same underlying vertex type.
* `SimpleGraph.Free` is the predicate that `H` is `G`-free, that is, `H` does not contain a copy of
  `G`. This is the negation of `SimpleGraph.IsContained` implemented for convenience.
* `SimpleGraph.killCopies G H`: Subgraph of `G` that does not contain `H`. Obtained by arbitrarily
  removing an edge from each copy of `H` in `G`.
* `SimpleGraph.copyCount G H`: Number of copies of `H` in `G`, i.e. number of subgraphs of `G`
  isomorphic to `H`.
* `SimpleGraph.labelledCopyCount G H`: Number of labelled copies of `H` in `G`, i.e. number of
  graph embeddings from `H` to `G`.

Induced containment:
* Induced copies of `G` inside `H` are already defined as `G ↪g H`.
* `SimpleGraph.IsIndContained G H` : `G` is contained as an induced subgraph in `H`.

## Notation

The following notation is declared in scope `SimpleGraph`:
* `G ⊑ H` for `SimpleGraph.IsContained G H`.
* `G ⊴ H` for `SimpleGraph.IsIndContained G H`.

## TODO

* Relate `⊥ ⊴ H` to there being an independent set in `H`.
* Count induced copies of a graph inside another.
* Make `copyCount`/`labelledCopyCount` computable (not necessarily efficiently).
-/

open Finset Function

open Fintype (card)

namespace SimpleGraph

variable {V W X α β γ : Type*} {G G₁ G₂ G₃ : SimpleGraph V} {H : SimpleGraph W} {I : SimpleGraph X}
  {A : SimpleGraph α} {B : SimpleGraph β} {C : SimpleGraph γ}

/-!
### Copies

#### Not necessarily induced copies

A copy of a subgraph `G` inside a subgraph `H` is an embedding of the vertices of `G` into the
vertices of `H`, such that adjacency in `G` implies adjacency in `H`.

We capture this concept by injective graph homomorphisms.
-/

section Copy

structure Copy (A : SimpleGraph α) (B : SimpleGraph β) where
  /-- A copy gives rise to a homomorphism. -/
  toHom : A →g B
  injective' : Injective toHom

abbrev Hom.toCopy (f : A →g B) (h : Injective f) : Copy A B := .mk f h

abbrev Embedding.toCopy (f : A ↪g B) : Copy A B := f.toHom.toCopy f.injective

abbrev Iso.toCopy (f : A ≃g B) : Copy A B := f.toEmbedding.toCopy

namespace Copy

-- INSTANCE (free from Core): :

lemma injective (f : Copy A B) : Injective f.toHom := f.injective'
