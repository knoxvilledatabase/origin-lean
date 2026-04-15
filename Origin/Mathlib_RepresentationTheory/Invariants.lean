/-
Extracted from RepresentationTheory/Invariants.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Subspace of invariants a group representation

This file introduces the subspace of invariants of a group representation
and proves basic results about it.
The main tool used is the average of all elements of the group, seen as an element of `k[G]`.
The action of this special element gives a projection onto the subspace of invariants.
In order for the definition of the average element to make sense, we need to assume for most of the
results that the order of `G` is invertible in `k` (e. g. `k` has characteristic `0`).
-/

suppress_compilation

universe w u v

open MonoidAlgebra

open Representation

namespace GroupAlgebra

variable (k G : Type*) [CommSemiring k] [Group G]

variable [Fintype G] [Invertible (Fintype.card G : k)]

noncomputable def average : k[G] := ⅟(Fintype.card G : k) • ∑ g : G, of k G g
