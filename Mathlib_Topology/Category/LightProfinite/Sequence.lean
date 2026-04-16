/-
Extracted from Topology/Category/LightProfinite/Sequence.lean
Genuine: 4 | Conflates: 0 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core
import Mathlib.Topology.Compactification.OnePoint
import Mathlib.Topology.Category.LightProfinite.Basic

noncomputable section

/-!

# The light profinite set classifying convergent sequences

This files defines the light profinite set `ℕ∪{∞}`, defined as the one point compactification of
`ℕ`.
-/

open CategoryTheory OnePoint TopologicalSpace Topology

namespace LightProfinite

noncomputable def natUnionInftyEmbedding : C(OnePoint ℕ, ℝ) where
  toFun
    | ∞ => 0
    | OnePoint.some n => 1 / (n+1 : ℝ)
  continuous_toFun := OnePoint.continuous_iff_from_nat _ |>.mpr
    tendsto_one_div_add_atTop_nhds_zero_nat

lemma isClosedEmbedding_natUnionInftyEmbedding : IsClosedEmbedding natUnionInftyEmbedding := by
  refine .of_continuous_injective_isClosedMap
    natUnionInftyEmbedding.continuous ?_ ?_
  · rintro (_|n) (_|m) h
    · rfl
    · simp only [natUnionInftyEmbedding, one_div, ContinuousMap.coe_mk, zero_eq_inv] at h
      rw [← Nat.cast_one, ← Nat.cast_add, eq_comm, Nat.cast_eq_zero] at h
      simp at h
    · simp only [natUnionInftyEmbedding, one_div, ContinuousMap.coe_mk, inv_eq_zero] at h
      rw [← Nat.cast_one, ← Nat.cast_add, Nat.cast_eq_zero] at h
      simp at h
    · simp only [natUnionInftyEmbedding, one_div, ContinuousMap.coe_mk, inv_inj, add_left_inj,
        Nat.cast_inj] at h
      rw [h]
  · exact fun _ hC => (hC.isCompact.image natUnionInftyEmbedding.continuous).isClosed

alias closedEmbedding_natUnionInftyEmbedding := isClosedEmbedding_natUnionInftyEmbedding

instance : MetrizableSpace (OnePoint ℕ) := isClosedEmbedding_natUnionInftyEmbedding.metrizableSpace

abbrev NatUnionInfty : LightProfinite := of (OnePoint ℕ)

scoped notation "ℕ∪{∞}" => NatUnionInfty

instance : Coe ℕ ℕ∪{∞} := optionCoe

open Filter Topology

lemma continuous_iff_convergent {Y : Type*} [TopologicalSpace Y] (f : ℕ∪{∞} → Y) :
    Continuous f ↔ Tendsto (fun x : ℕ ↦ f x) atTop (𝓝 (f ∞)) :=
  continuous_iff_from_nat f

end LightProfinite
