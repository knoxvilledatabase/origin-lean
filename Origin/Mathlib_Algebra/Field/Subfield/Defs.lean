/-
Extracted from Algebra/Field/Subfield/Defs.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Subfields

Let `K` be a division ring, for example a field.
This file defines the "bundled" subfield type `Subfield K`, a type
whose terms correspond to subfields of `K`. Note we do not require the "subfields" to be
commutative, so they are really sub-division rings / skew fields. This is the preferred way to talk
about subfields in mathlib. Unbundled subfields (`s : Set K` and `IsSubfield s`)
are not in this file, and they will ultimately be deprecated.

We prove that subfields are a complete lattice, and that you can `map` (pushforward) and
`comap` (pull back) them along ring homomorphisms.

We define the `closure` construction from `Set K` to `Subfield K`, sending a subset of `K`
to the subfield it generates, and prove that it is a Galois insertion.

## Main definitions

Notation used here:

`(K : Type u) [DivisionRing K] (L : Type u) [DivisionRing L] (f g : K →+* L)`
`(A : Subfield K) (B : Subfield L) (s : Set K)`

* `Subfield K` : the type of subfields of a division ring `K`.

## Implementation notes

A subfield is implemented as a subring which is closed under `⁻¹`.

Lattice inclusion (e.g. `≤` and `⊓`) is used rather than set notation (`⊆` and `∩`), although
`∈` is defined as membership of a subfield's underlying set.

## Tags
subfield, subfields
-/

universe u v w

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

class SubfieldClass (S K : Type*) [DivisionRing K] [SetLike S K] : Prop
    extends SubringClass S K, InvMemClass S K

namespace SubfieldClass

variable (S : Type*) [SetLike S K] [h : SubfieldClass S K]

-- INSTANCE (free from Core): (priority

variable {S} {x : K}
