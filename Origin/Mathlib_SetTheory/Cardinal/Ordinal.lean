/-
Extracted from SetTheory/Cardinal/Ordinal.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Ordinal arithmetic with cardinals

This file collects results about the cardinality of different ordinal operations.
-/

universe u v

open Cardinal Ordinal Set

/-! ### Cardinal operations with ordinal indices -/

namespace Cardinal

lemma mk_biUnion_le_of_le_lift {β : Type v} {o : Ordinal.{u}} {c : Cardinal.{v}}
    (ho : lift.{v} o.card ≤ lift.{u} c) (hc : ℵ₀ ≤ c) (A : Ordinal → Set β)
    (hA : ∀ j < o, #(A j) ≤ c) : #(⋃ j < o, A j) ≤ c := by
  simp_rw [← mem_Iio, biUnion_eq_iUnion, iUnion, iSup, ← ToType.mk.symm.surjective.range_comp]
  rw [← lift_le.{u}]
  apply ((mk_iUnion_le_lift _).trans _).trans_eq (mul_eq_self (aleph0_le_lift.2 hc))
  rw [mk_toType]
  refine mul_le_mul' ho (ciSup_le' ?_)
  intro i
  simpa using hA _ i.toOrd.prop
