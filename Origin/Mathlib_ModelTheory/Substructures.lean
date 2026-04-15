/-
Extracted from ModelTheory/Substructures.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# First-Order Substructures

This file defines substructures of first-order structures in a similar manner to the various
substructures appearing in the algebra library.

## Main Definitions

- A `FirstOrder.Language.Substructure` is defined so that `L.Substructure M` is the type of all
    substructures of the `L`-structure `M`.
- `FirstOrder.Language.Substructure.closure` is defined so that if `s : Set M`, `closure L s` is
    the least substructure of `M` containing `s`.
- `FirstOrder.Language.Substructure.comap` is defined so that `s.comap f` is the preimage of the
    substructure `s` under the homomorphism `f`, as a substructure.
- `FirstOrder.Language.Substructure.map` is defined so that `s.map f` is the image of the
    substructure `s` under the homomorphism `f`, as a substructure.
- `FirstOrder.Language.Hom.range` is defined so that `f.range` is the range of the
    homomorphism `f`, as a substructure.
- `FirstOrder.Language.Hom.domRestrict` and `FirstOrder.Language.Hom.codRestrict` restrict
    the domain and codomain respectively of first-order homomorphisms to substructures.
- `FirstOrder.Language.Embedding.domRestrict` and `FirstOrder.Language.Embedding.codRestrict`
    restrict the domain and codomain respectively of first-order embeddings to substructures.
- `FirstOrder.Language.Substructure.inclusion` is the inclusion embedding between substructures.
- `FirstOrder.Language.Substructure.PartialEquiv` is defined so that `PartialEquiv L M N` is
  the type of equivalences between substructures of `M` and `N`.

## Main Results

- `L.Substructure M` forms a `CompleteLattice`.
-/

universe u v w

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {M : Type w} {N P : Type*}

variable [L.Structure M] [L.Structure N] [L.Structure P]

open FirstOrder Cardinal

open Structure

section ClosedUnder

open Set

variable {n : ℕ} (f : L.Functions n) (s : Set M)

def ClosedUnder : Prop :=
  ∀ x : Fin n → M, (∀ i : Fin n, x i ∈ s) → funMap f x ∈ s

variable (L)
