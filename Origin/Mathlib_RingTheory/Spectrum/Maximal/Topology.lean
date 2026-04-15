/-
Extracted from RingTheory/Spectrum/Maximal/Topology.lean
Genuine: 2 of 4 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# The Zariski topology on the maximal spectrum of a commutative (semi)ring

## Implementation notes

The Zariski topology on the maximal spectrum is defined as the subspace topology induced by the
natural inclusion into the prime spectrum to avoid API duplication for zero loci.
-/

noncomputable section

universe u v

variable (R : Type u) [CommRing R]

variable {R}

namespace MaximalSpectrum

open PrimeSpectrum Set

theorem toPrimeSpectrum_range :
    Set.range (@toPrimeSpectrum R _) = { x | IsClosed ({x} : Set <| PrimeSpectrum R) } := by
  simp only [isClosed_singleton_iff_isMaximal]
  ext ⟨x, _⟩
  exact ⟨fun ⟨y, hy⟩ => hy ▸ y.isMaximal, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩

-- INSTANCE (free from Core): zariskiTopology

-- INSTANCE (free from Core): :

theorem toPrimeSpectrum_continuous : Continuous <| @toPrimeSpectrum R _ :=
  continuous_induced_dom

end MaximalSpectrum
