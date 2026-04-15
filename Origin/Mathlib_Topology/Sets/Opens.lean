/-
Extracted from Topology/Sets/Opens.lean
Genuine: 2 of 6 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# Open sets

## Summary

We define the subtype of open sets in a topological space.

## Main Definitions

### Bundled open sets

- `TopologicalSpace.Opens α` is the type of open subsets of a topological space `α`.
- `TopologicalSpace.Opens.IsBasis` is a predicate saying that a set of `Opens`s form a topological
  basis.
- `TopologicalSpace.Opens.comap`: preimage of an open set under a continuous map as a `FrameHom`.
- `Homeomorph.opensCongr`: order-preserving equivalence between open sets in the domain and the
  codomain of a homeomorphism.

### Bundled open neighborhoods

- `TopologicalSpace.OpenNhdsOf x` is the type of open subsets of a topological space `α` containing
  `x : α`.
- `TopologicalSpace.OpenNhdsOf.comap f x U` is the preimage of open neighborhood `U` of `f x` under
  `f : C(α, β)`.

## Main results

We define order structures on both `Opens α` (`CompleteLattice`, `Frame`) and `OpenNhdsOf x`
(`OrderTop`, `DistribLattice`).

## TODO

- Rename `TopologicalSpace.Opens` to `Open`?
- Port the `auto_cases` tactic version (as a plugin if the ported `auto_cases` will allow plugins).
-/

open Filter Function Order Set

open Topology

variable {ι α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]

namespace TopologicalSpace

variable (α) in

structure Opens where
  /-- The underlying set of a bundled `TopologicalSpace.Opens` object. -/
  carrier : Set α
  /-- The `TopologicalSpace.Opens.carrier _` is an open set. -/
  is_open' : IsOpen carrier

namespace Opens

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): instSecondCountableOpens

theorem «forall» {p : Opens α → Prop} : (∀ U, p U) ↔ ∀ (U : Set α) (hU : IsOpen U), p ⟨U, hU⟩ :=
  ⟨fun h _ _ => h _, fun h _ => h _ _⟩
