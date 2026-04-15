/-
Extracted from Topology/Algebra/Nonarchimedean/AdicTopology.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Adic topology

Given a commutative ring `R` and an ideal `I` in `R`, this file constructs the unique
topology on `R` which is compatible with the ring structure and such that a set is a neighborhood
of zero if and only if it contains a power of `I`. This topology is non-archimedean: every
neighborhood of zero contains an open subgroup, namely a power of `I`.

It also studies the predicate `IsAdic` which states that a given topological ring structure is
adic, proving a characterization and showing that raising an ideal to a positive power does not
change the associated topology.

Finally, it defines `WithIdeal`, a class registering an ideal in a ring and providing the
corresponding adic topology to the type class inference system.


## Main definitions and results

* `Ideal.adic_basis`: the basis of submodules given by powers of an ideal.
* `Ideal.adicTopology`: the adic topology associated to an ideal. It has the above basis
  for neighborhoods of zero.
* `Ideal.nonarchimedean`: the adic topology is non-archimedean
* `isAdic_iff`: A topological ring is `J`-adic if and only if it admits the powers of `J` as
  a basis of open neighborhoods of zero.
* `WithIdeal`: a class registering an ideal in a ring.

## Implementation notes

The `I`-adic topology on a ring `R` has a contrived definition using `I^n • ⊤` instead of `I`
to make sure it is definitionally equal to the `I`-topology on `R` seen as an `R`-module.

-/

variable {R : Type*} [CommRing R]

open Set IsTopologicalAddGroup Submodule Filter

open Topology Pointwise

namespace Ideal

theorem adic_basis (I : Ideal R) : SubmodulesRingBasis fun n : ℕ => (I ^ n • ⊤ : Ideal R) :=
  { inter := by
      suffices ∀ i j : ℕ, ∃ k, I ^ k ≤ I ^ i ∧ I ^ k ≤ I ^ j by
        simpa only [smul_eq_mul, mul_top, Algebra.algebraMap_self, map_id, le_inf_iff] using this
      intro i j
      exact ⟨max i j, pow_le_pow_right (le_max_left i j), pow_le_pow_right (le_max_right i j)⟩
    leftMul := by
      suffices ∀ (a : R) (i : ℕ), ∃ j : ℕ, a • I ^ j ≤ I ^ i by
        simpa only [smul_top_eq_map, Algebra.algebraMap_self, map_id] using this
      intro r n
      use n
      rintro a ⟨x, hx, rfl⟩
      exact (I ^ n).smul_mem r hx
    mul := by
      suffices ∀ i : ℕ, ∃ j : ℕ, (↑(I ^ j) * ↑(I ^ j) : Set R) ⊆ (↑(I ^ i) : Set R) by
        simpa only [smul_top_eq_map, Algebra.algebraMap_self, map_id] using this
      intro n
      use n
      rintro a ⟨x, _hx, b, hb, rfl⟩
      exact (I ^ n).smul_mem x hb }
