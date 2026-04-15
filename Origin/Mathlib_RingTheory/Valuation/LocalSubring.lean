/-
Extracted from RingTheory/Valuation/LocalSubring.lean
Genuine: 3 of 5 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!

# Valuation subrings are exactly the maximal local subrings

See `LocalSubring.isMax_iff`.
Note that the order on local subrings is not merely inclusion but domination.

-/

open IsLocalRing Algebra

variable {R S K : Type*} [CommRing R] [CommRing S] [Field K]

-- INSTANCE (free from Core): (V

-- INSTANCE (free from Core): (V

def ValuationSubring.toLocalSubring (A : ValuationSubring K) : LocalSubring K where
  toSubring := A.toSubring
  isLocalRing := A.isLocalRing

lemma ValuationSubring.toLocalSubring_injective :
    Function.Injective (ValuationSubring.toLocalSubring (K := K)) :=
  fun _ _ h ↦ ValuationSubring.toSubring_injective congr(($h).toSubring)

lemma LocalSubring.map_maximalIdeal_eq_top_of_isMax {R : LocalSubring K}
    (hR : IsMax R) {S : Subring K} (hS : R.toSubring < S) :
    (maximalIdeal R.toSubring).map (Subring.inclusion hS.le) = ⊤ := by
  set mR := (maximalIdeal R.toSubring).map (Subring.inclusion hS.le)
  by_contra h_is_not_top
  obtain ⟨M, h_is_max, h_incl⟩ := Ideal.exists_le_maximal _ h_is_not_top
  let fSₘ : LocalSubring K := LocalSubring.ofPrime S M
  have h_RleSₘ : R ≤ fSₘ := by
    refine ⟨hS.le.trans (LocalSubring.le_ofPrime ..), ((local_hom_TFAE _).out 2 0).mp ?_⟩
    conv_rhs => rw [← IsLocalization.AtPrime.map_eq_maximalIdeal M]
    refine .trans ?_ (Ideal.map_mono h_incl)
    rw [Ideal.map_map]; rfl
  exact (hR.eq_of_le h_RleSₘ ▸ hS).not_ge (LocalSubring.le_ofPrime ..)
