/-
Extracted from RingTheory/Spectrum/Prime/TensorProduct.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Lemmas regarding the prime spectrum of tensor products

## Main result
- `PrimeSpectrum.isEmbedding_tensorProductTo_of_surjectiveOnStalks`:
  If `R →+* T` is surjective on stalks (see `Mathlib/RingTheory/SurjectiveOnStalks.lean`),
  then `Spec(S ⊗[R] T) → Spec S × Spec T` is a topological embedding
  (where `Spec S × Spec T` is the Cartesian product with the product topology).
-/

variable (R S T : Type*) [CommRing R] [CommRing S] [Algebra R S]

variable [CommRing T] [Algebra R T]

open TensorProduct Topology

noncomputable

def PrimeSpectrum.tensorProductTo (x : PrimeSpectrum (S ⊗[R] T)) :
    PrimeSpectrum S × PrimeSpectrum T :=
  ⟨comap (algebraMap _ _) x, comap Algebra.TensorProduct.includeRight.toRingHom x⟩
