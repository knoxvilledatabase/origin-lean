/-
Extracted from ModelTheory/PartialEquiv.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Partial Isomorphisms
This file defines partial isomorphisms between first-order structures.

## Main Definitions
- `FirstOrder.Language.PartialEquiv` is defined so that `L.PartialEquiv M N`, annotated
  `M ≃ₚ[L] N`, is the type of equivalences between substructures of `M` and `N`. These can be
  ordered, with an order that is defined here in terms of a commutative square, but could also be
  defined as the order on the graphs of the partial equivalences under inclusion as subsets of
  `M × N`.
- `FirstOrder.Language.FGEquiv` is the type of partial equivalences `M ≃ₚ[L] N` with
  finitely-generated domain (or equivalently, codomain).
- `FirstOrder.Language.IsExtensionPair` is defined so that `L.IsExtensionPair M N` indicates that
  any finitely-generated partial equivalence from `M` to `N` can be extended to include an arbitrary
  element `m : M` in its domain.

## Main Results
- `FirstOrder.Language.embedding_from_cg` shows that if structures `M` and `N` form an equivalence
  pair with `M` countably-generated, then any finite-generated partial equivalence between them
  can be extended to an embedding `M ↪[L] N`.
- `FirstOrder.Language.equiv_from_cg` shows that if countably-generated structures `M` and `N` form
  an equivalence pair in both directions, then any finite-generated partial equivalence between them
  can be extended to an isomorphism `M ↪[L] N`.
- The proofs of these results are adapted in part from David Wärn's approach to countable dense
  linear orders, a special case of this phenomenon in the case where `L = Language.order`.

-/

universe u v w w'

namespace FirstOrder

namespace Language

variable (L : Language.{u, v}) (M : Type w) (N : Type w')

variable [L.Structure M] [L.Structure N]

open FirstOrder Structure Substructure

structure PartialEquiv where
  /-- The substructure which is the domain of the equivalence. -/
  dom : L.Substructure M
  /-- The substructure which is the codomain of the equivalence. -/
  cod : L.Substructure N
  /-- The equivalence between the two subdomains. -/
  toEquiv : dom ≃[L] cod
