/-
Extracted from Algebra/Field/Subfield/Basic.lean
Genuine: 4 of 6 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Subfields

Let `K` be a division ring, for example a field.
This file concerns the "bundled" subfield type `Subfield K`, a type
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

* `instance : CompleteLattice (Subfield K)` : the complete lattice structure on the subfields.

* `Subfield.closure` : subfield closure of a set, i.e., the smallest subfield that includes the set.

* `Subfield.gi` : `closure : Set M → Subfield M` and coercion `(↑) : Subfield M → Set M`
  form a `GaloisInsertion`.

* `comap f B : Subfield K` : the preimage of a subfield `B` along the ring homomorphism `f`

* `map f A : Subfield L` : the image of a subfield `A` along the ring homomorphism `f`.

* `f.fieldRange : Subfield L` : the range of the ring homomorphism `f`.

* `eqLocusField f g : Subfield K` : given ring homomorphisms `f g : K →+* R`,
     the subfield of `K` where `f x = g x`

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

namespace Subfield

variable (s t : Subfield K)

section DerivedFromSubfieldClass

protected theorem list_prod_mem {l : List K} : (∀ x ∈ l, x ∈ s) → l.prod ∈ s :=
  list_prod_mem

protected theorem list_sum_mem {l : List K} : (∀ x ∈ l, x ∈ s) → l.sum ∈ s :=
  list_sum_mem

protected theorem multiset_sum_mem (m : Multiset K) : (∀ a ∈ m, a ∈ s) → m.sum ∈ s :=
  multiset_sum_mem m

protected theorem sum_mem {ι : Type*} {t : Finset ι} {f : ι → K} (h : ∀ c ∈ t, f c ∈ s) :
    (∑ i ∈ t, f i) ∈ s :=
  sum_mem h

end DerivedFromSubfieldClass

/-! ### top -/

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :
