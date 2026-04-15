/-
Extracted from Order/Sublattice.lean
Genuine: 4 of 6 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Sublattices

This file defines sublattices.

## TODO

Subsemilattices, if people care about them.

## Tags

sublattice
-/

open Function Set

variable {ι : Sort*} (α β γ : Type*) [Lattice α] [Lattice β] [Lattice γ]

structure Sublattice where
  /-- The underlying set of a sublattice. **Do not use directly**. Instead, use the coercion
  `Sublattice α → Set α`, which Lean should automatically insert for you in most cases. -/
  carrier : Set α
  supClosed' : SupClosed carrier
  infClosed' : InfClosed carrier

variable {α β γ}

namespace Sublattice

variable {L M : Sublattice α} {f : LatticeHom α β} {s t : Set α} {a b : α}

-- INSTANCE (free from Core): instSetLike

-- INSTANCE (free from Core): :

def Simps.coe (L : Sublattice α) : Set α := L

initialize_simps_projections Sublattice (carrier → coe, as_prefix coe)

abbrev ofIsSublattice (s : Set α) (hs : IsSublattice s) : Sublattice α := ⟨s, hs.1, hs.2⟩

lemma coe_inj : (L : Set α) = M ↔ L = M := SetLike.coe_set_eq
