/-
Extracted from RingTheory/NonUnitalSubring/Basic.lean
Genuine: 3 of 4 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# `NonUnitalSubring`s

Let `R` be a non-unital ring.
We prove that non-unital subrings are a complete lattice, and that you can `map` (pushforward) and
`comap` (pull back) them along ring homomorphisms.

We define the `closure` construction from `Set R` to `NonUnitalSubring R`, sending a subset of
`R` to the non-unital subring it generates, and prove that it is a Galois insertion.

## Main definitions

Notation used here:

`(R : Type u) [NonUnitalRing R] (S : Type u) [NonUnitalRing S] (f g : R →ₙ+* S)`
`(A : NonUnitalSubring R) (B : NonUnitalSubring S) (s : Set R)`

* `instance : CompleteLattice (NonUnitalSubring R)` : the complete lattice structure on the
  non-unital subrings.

* `NonUnitalSubring.center` : the center of a non-unital ring `R`.

* `NonUnitalSubring.closure` : non-unital subring closure of a set, i.e., the smallest
  non-unital subring that includes the set.

* `NonUnitalSubring.gi` : `closure : Set M → NonUnitalSubring M` and coercion
  `coe : NonUnitalSubring M → Set M`
  form a `GaloisInsertion`.

* `comap f B : NonUnitalSubring A` : the preimage of a non-unital subring `B` along the
  non-unital ring homomorphism `f`

* `map f A : NonUnitalSubring B` : the image of a non-unital subring `A` along the
  non-unital ring homomorphism `f`.

* `Prod A B : NonUnitalSubring (R × S)` : the product of non-unital subrings

* `f.range : NonUnitalSubring B` : the range of the non-unital ring homomorphism `f`.

* `eq_locus f g : NonUnitalSubring R` : given non-unital ring homomorphisms `f g : R →ₙ+* S`,
     the non-unital subring of `R` where `f x = g x`

## Implementation notes

A non-unital subring is implemented as a `NonUnitalSubsemiring` which is also an
additive subgroup.

Lattice inclusion (e.g. `≤` and `⊓`) is used rather than set notation (`⊆` and `∩`), although
`∈` is defined as membership of a non-unital subring's underlying set.

## Tags
non-unital subring
-/

universe u v w

section Basic

variable {R : Type u} {S : Type v} [NonUnitalNonAssocRing R]

namespace NonUnitalSubring

variable (s : NonUnitalSubring R)

protected theorem list_sum_mem {l : List R} : (∀ x ∈ l, x ∈ s) → l.sum ∈ s :=
  list_sum_mem

protected theorem multiset_sum_mem {R} [NonUnitalNonAssocRing R] (s : NonUnitalSubring R)
    (m : Multiset R) : (∀ a ∈ m, a ∈ s) → m.sum ∈ s :=
  multiset_sum_mem _

protected theorem sum_mem {R : Type*} [NonUnitalNonAssocRing R] (s : NonUnitalSubring R)
    {ι : Type*} {t : Finset ι} {f : ι → R} (h : ∀ c ∈ t, f c ∈ s) : (∑ i ∈ t, f i) ∈ s :=
  sum_mem h

/-! ## top -/

-- INSTANCE (free from Core): :
