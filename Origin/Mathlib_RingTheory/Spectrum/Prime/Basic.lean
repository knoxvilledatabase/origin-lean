/-
Extracted from RingTheory/Spectrum/Prime/Basic.lean
Genuine: 4 of 6 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Prime spectrum of a commutative (semi)ring

For the Zariski topology, see `Mathlib/RingTheory/Spectrum/Prime/Topology.lean`.

(It is also naturally endowed with a sheaf of rings,
which is constructed in `AlgebraicGeometry.StructureSheaf`.)

## Main definitions

* `zeroLocus s`: The zero locus of a subset `s` of `R`
  is the subset of `PrimeSpectrum R` consisting of all prime ideals that contain `s`.
* `vanishingIdeal t`: The vanishing ideal of a subset `t` of `PrimeSpectrum R`
  is the intersection of points in `t` (viewed as prime ideals).

## Conventions

We denote subsets of (semi)rings with `s`, `s'`, etc...
whereas we denote subsets of prime spectra with `t`, `t'`, etc...

## Inspiration/contributors

The contents of this file draw inspiration from <https://github.com/ramonfmir/lean-scheme>
which has contributions from Ramon Fernandez Mir, Kevin Buzzard, Kenny Lau,
and Chris Hughes (on an earlier repository).

## References
* [M. F. Atiyah and I. G. Macdonald, *Introduction to commutative algebra*][atiyah-macdonald]
* [P. Samuel, *Algebraic Theory of Numbers*][samuel1967]
-/

assert_not_exists TopologicalSpace

noncomputable section

open scoped Pointwise

universe u v

variable (R : Type u) (S : Type v)

namespace PrimeSpectrum

section CommSemiRing

variable [CommSemiring R] [CommSemiring S]

variable {R S}

lemma nonempty_iff_nontrivial : Nonempty (PrimeSpectrum R) ↔ Nontrivial R := by
  refine ⟨fun ⟨p⟩ ↦ ⟨0, 1, fun h ↦ p.2.ne_top ?_⟩, fun h ↦ ?_⟩
  · simp [Ideal.eq_top_iff_one p.asIdeal, ← h]
  · obtain ⟨I, hI⟩ := Ideal.exists_maximal R
    exact ⟨⟨I, hI.isPrime⟩⟩

lemma isEmpty_iff_subsingleton : IsEmpty (PrimeSpectrum R) ↔ Subsingleton R := by
  contrapose!; exact nonempty_iff_nontrivial

-- INSTANCE (free from Core): [Nontrivial

-- INSTANCE (free from Core): [Subsingleton

lemma nontrivial (p : PrimeSpectrum R) : Nontrivial R :=
  nonempty_iff_nontrivial.mp ⟨p⟩

variable (R S)

theorem range_asIdeal : Set.range PrimeSpectrum.asIdeal = {J : Ideal R | J.IsPrime} :=
  Set.ext fun J ↦
    ⟨fun hJ ↦ let ⟨j, hj⟩ := Set.mem_range.mp hJ; Set.mem_setOf.mpr <| hj ▸ j.isPrime,
      fun hJ ↦ Set.mem_range.mpr ⟨⟨J, Set.mem_setOf.mp hJ⟩, rfl⟩⟩
