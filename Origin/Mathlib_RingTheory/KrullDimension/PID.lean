/-
Extracted from RingTheory/KrullDimension/PID.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# The Krull dimension of a principal ideal domain

In this file, we proved some results about the dimension of a principal ideal domain.
-/

-- INSTANCE (free from Core): IsPrincipalIdealRing.krullDimLE_one

theorem IsPrincipalIdealRing.ringKrullDim_eq_one (R : Type*) [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] (h : ¬ IsField R) : ringKrullDim R = 1 := by
  apply eq_of_le_of_not_lt ?_ fun h' ↦ h ?_
  · rw [← Nat.cast_one, ← Ring.krullDimLE_iff]
    infer_instance
  · have h'' : ringKrullDim R ≤ 0 := Order.le_of_lt_succ h'
    rw [← Nat.cast_zero, ← Ring.krullDimLE_iff] at h''
    exact Ring.KrullDimLE.isField_of_isDomain

lemma IsPrincipalIdealRing.height_eq_one_of_isMaximal {R : Type*} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] (m : Ideal R) [m.IsMaximal] (h : ¬ IsField R) :
    m.height = 1 := by
  refine le_antisymm ?_ ?_
  · suffices h : (m.height : WithBot ℕ∞) ≤ 1 by norm_cast at h
    rw [← IsPrincipalIdealRing.ringKrullDim_eq_one _ h]
    exact Ideal.height_le_ringKrullDim_of_ne_top Ideal.IsPrime.ne_top'
  · rw [Order.one_le_iff_pos, Ideal.height_eq_primeHeight, Ideal.primeHeight, Order.height_pos]
    exact not_isMin_of_lt (b := ⊥) (Ideal.bot_lt_of_maximal m h)
