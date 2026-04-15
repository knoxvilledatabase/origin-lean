/-
Extracted from Algebra/Category/Ring/Instances.lean
Genuine: 1 of 5 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# Ring-theoretic results in terms of categorical language
-/

universe u

open CategoryTheory

-- INSTANCE (free from Core): localization_unit_isIso

-- INSTANCE (free from Core): localization_unit_isIso'

theorem IsLocalization.epi {R : Type*} [CommRing R] (M : Submonoid R) (S : Type _) [CommRing S]
    [Algebra R S] [IsLocalization M S] : Epi (CommRingCat.ofHom <| algebraMap R S) :=
  ⟨fun _ _ h => CommRingCat.hom_ext <| ringHom_ext M congr(($h).hom)⟩

-- INSTANCE (free from Core): Localization.epi

-- INSTANCE (free from Core): Localization.epi'
