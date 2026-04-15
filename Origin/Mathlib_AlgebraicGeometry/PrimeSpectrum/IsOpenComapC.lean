/-
Extracted from AlgebraicGeometry/PrimeSpectrum/IsOpenComapC.lean
Genuine: 5 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.AlgebraicGeometry.PrimeSpectrum.Basic
import Mathlib.RingTheory.Polynomial.Basic

/-!
The morphism `Spec R[x] --> Spec R` induced by the natural inclusion `R --> R[x]` is an open map.

The main result is the first part of the statement of Lemma 00FB in the Stacks Project.

https://stacks.math.columbia.edu/tag/00FB
-/

open Ideal Polynomial PrimeSpectrum Set

namespace AlgebraicGeometry

namespace Polynomial

variable {R : Type*} [CommRing R] {f : R[X]}

def imageOfDf (f : R[X]) : Set (PrimeSpectrum R) :=
  { p : PrimeSpectrum R | ∃ i : ℕ, coeff f i ∉ p.asIdeal }

theorem isOpen_imageOfDf : IsOpen (imageOfDf f) := by
  rw [imageOfDf, setOf_exists fun i (x : PrimeSpectrum R) => coeff f i ∉ x.asIdeal]
  exact isOpen_iUnion fun i => isOpen_basicOpen

theorem comap_C_mem_imageOfDf {I : PrimeSpectrum R[X]}
    (H : I ∈ (zeroLocus {f} : Set (PrimeSpectrum R[X]))ᶜ) :
    PrimeSpectrum.comap (Polynomial.C : R →+* R[X]) I ∈ imageOfDf f :=
  exists_C_coeff_not_mem (mem_compl_zeroLocus_iff_not_mem.mp H)

theorem imageOfDf_eq_comap_C_compl_zeroLocus :
    imageOfDf f = PrimeSpectrum.comap (C : R →+* R[X]) '' (zeroLocus {f})ᶜ := by
  ext x
  refine ⟨fun hx => ⟨⟨map C x.asIdeal, isPrime_map_C_of_isPrime x.isPrime⟩, ⟨?_, ?_⟩⟩, ?_⟩
  · rw [mem_compl_iff, mem_zeroLocus, singleton_subset_iff]
    cases' hx with i hi
    exact fun a => hi (mem_map_C_iff.mp a i)
  · ext x
    refine ⟨fun h => ?_, fun h => subset_span (mem_image_of_mem C.1 h)⟩
    rw [← @coeff_C_zero R x _]
    exact mem_map_C_iff.mp h 0
  · rintro ⟨xli, complement, rfl⟩
    exact comap_C_mem_imageOfDf complement

theorem isOpenMap_comap_C : IsOpenMap (PrimeSpectrum.comap (C : R →+* R[X])) := by
  rintro U ⟨s, z⟩
  rw [← compl_compl U, ← z, ← iUnion_of_singleton_coe s, zeroLocus_iUnion, compl_iInter,
    image_iUnion]
  simp_rw [← imageOfDf_eq_comap_C_compl_zeroLocus]
  exact isOpen_iUnion fun f => isOpen_imageOfDf

end Polynomial

end AlgebraicGeometry
