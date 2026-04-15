/-
Extracted from Data/Real/Hom.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Uniqueness of ring homomorphisms to the real numbers

This file contains results about ring homomorphisms to `ℝ`.

## Main results

* `Real.nonemptyOrderRingHom`: For any archimedean ordered field `α`, there exists
  a monotone ring homomorphism `α →+*o ℝ`.
* `Real.RingHom.unique`: There exists no nontrivial ring homomorphism `ℝ →+* ℝ`.
-/

-- INSTANCE (free from Core): Real.nonemptyOrderRingHom

theorem ringHom_monotone {R S : Type*} [Ring R] [PartialOrder R] [IsOrderedAddMonoid R]
    [Ring S] [LinearOrder S] [IsOrderedAddMonoid S] [PosMulMono S]
    (hR : ∀ r : R, 0 ≤ r → IsSquare r) (f : R →+* S) : Monotone f :=
  (monotone_iff_map_nonneg f).2 fun r h => by
    obtain ⟨s, rfl⟩ := hR r h; rw [map_mul]; apply mul_self_nonneg

-- INSTANCE (free from Core): Real.RingHom.unique
