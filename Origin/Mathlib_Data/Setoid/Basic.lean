/-
Extracted from Data/Setoid/Basic.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Equivalence relations

This file defines the complete lattice of equivalence relations on a type, results about the
inductively defined equivalence closure of a binary relation, and the analogues of some isomorphism
theorems for quotients of arbitrary types.

## Implementation notes

The complete lattice instance for equivalence relations could have been defined by lifting
the Galois insertion of equivalence relations on α into binary relations on α, and then using
`CompleteLattice.copy` to define a complete lattice instance with more appropriate
definitional equalities (a similar example is `Filter.CompleteLattice` in
`Mathlib/Order/Filter/Basic.lean`). This does not save space, however, and is less clear.

Partitions are not defined as a separate structure here; users are encouraged to
reason about them using the existing `Setoid` and its infrastructure.

## Tags

setoid, equivalence, iseqv, relation, equivalence relation
-/

attribute [refl, simp] Setoid.refl

attribute [symm] Setoid.symm

attribute [trans] Setoid.trans

variable {α : Type*} {β : Type*}

namespace Setoid

attribute [ext] ext

theorem eq_iff_rel_eq {r₁ r₂ : Setoid α} : r₁ = r₂ ↔ ⇑r₁ = ⇑r₂ :=
  ⟨fun h => h ▸ rfl, fun h => Setoid.ext fun _ _ => h ▸ Iff.rfl⟩

-- INSTANCE (free from Core): :
