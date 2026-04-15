/-
Extracted from Combinatorics/SimpleGraph/Finsubgraph.lean
Genuine: 2 of 6 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# Homomorphisms from finite subgraphs

This file defines the type of finite subgraphs of a `SimpleGraph` and proves a compactness result
for homomorphisms to a finite codomain.

## Main statements

* `SimpleGraph.nonempty_hom_of_forall_finite_subgraph_hom`: If every finite subgraph of a (possibly
  infinite) graph `G` has a homomorphism to some finite graph `F`, then there is also a homomorphism
  `G →g F`.

## Notation

`→fg` is a module-local variant on `→g` where the domain is a finite subgraph of some supergraph
`G`.

## Implementation notes

The proof here uses compactness as formulated in `nonempty_sections_of_finite_inverse_system`. For
finite subgraphs `G'' ≤ G'`, the inverse system `finsubgraphHomFunctor` restricts homomorphisms
`G' →fg F` to domain `G''`.
-/

open Set CategoryTheory

universe u v

variable {V : Type u} {W : Type v} {G : SimpleGraph V} {F : SimpleGraph W}

namespace SimpleGraph

abbrev Finsubgraph (G : SimpleGraph V) :=
  { G' : G.Subgraph // G'.verts.Finite }

abbrev FinsubgraphHom (G' : G.Finsubgraph) (F : SimpleGraph W) :=
  G'.val.coe →g F

local infixl:50 " →fg " => FinsubgraphHom

namespace Finsubgraph

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): instSDiff
