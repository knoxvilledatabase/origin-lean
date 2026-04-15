/-
Extracted from RingTheory/KrullDimension/Basic.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Krull dimensions of (commutative) rings

Given a commutative ring, its ring-theoretic Krull dimension is the order-theoretic Krull dimension
of its prime spectrum. Unfolding this definition, it is the length of the longest sequence(s) of
prime ideals ordered by strict inclusion.
-/

open Order

noncomputable def ringKrullDim (R : Type*) [CommSemiring R] : WithBot ℕ∞ :=
  krullDim (PrimeSpectrum R)

abbrev Ring.KrullDimLE (n : ℕ) (R : Type*) [CommSemiring R] : Prop :=
  Order.KrullDimLE n (PrimeSpectrum R)

variable {R S : Type*} [CommSemiring R] [CommSemiring S]

lemma Ring.krullDimLE_iff {n : ℕ} :
    KrullDimLE n R ↔ ringKrullDim R ≤ n := Order.krullDimLE_iff n (PrimeSpectrum R)
