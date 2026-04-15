/-
Extracted from NumberTheory/ModularForms/ArithmeticSubgroups.lean
Genuine: 8 of 23 | Dissolved: 0 | Infrastructure: 15
-/
import Origin.Core

/-!
# Arithmetic subgroups of `GL(2, ℝ)`

We define a subgroup of `GL (Fin 2) ℝ` to be *arithmetic* if it is commensurable with the image
of `SL(2, ℤ)`.
-/

open Matrix Matrix.SpecialLinearGroup

open scoped MatrixGroups

local notation "SL" => SpecialLinearGroup

variable {n : Type*} [Fintype n] [DecidableEq n]

namespace Subgroup

section det_typeclasses

variable {R : Type*} [CommRing R] (Γ : Subgroup (GL n R))

class HasDetPlusMinusOne : Prop where
  det_eq {g} (hg : g ∈ Γ) : g.det = 1 ∨ g.det = -1

variable {Γ} in

lemma HasDetPlusMinusOne.abs_det [LinearOrder R] [IsOrderedRing R] [HasDetPlusMinusOne Γ]
    {g} (hg : g ∈ Γ) : |g.det.val| = 1 := by
  rcases HasDetPlusMinusOne.det_eq hg with h | h <;> simp [h]

lemma hasDetPlusMinusOne_iff_abs_det [LinearOrder R] [IsOrderedRing R] :
    HasDetPlusMinusOne Γ ↔ ∀ {g}, g ∈ Γ → |g.det.val| = 1 := by
  refine ⟨fun h {g} hg ↦ h.abs_det hg, fun h ↦ ⟨?_⟩⟩
  simpa [-GeneralLinearGroup.val_det_apply, abs_eq zero_le_one] using @h

class HasDetOne : Prop where
  det_eq {g} (hg : g ∈ Γ) : g.det = 1

-- INSTANCE (free from Core): (Γ

-- INSTANCE (free from Core): {S

-- INSTANCE (free from Core): {S

-- INSTANCE (free from Core): [HasDetOne

-- INSTANCE (free from Core): (Γ'

-- INSTANCE (free from Core): (Γ'

end det_typeclasses

section SL2Z_in_GL2R

scoped[MatrixGroups] notation "𝒮ℒ" => MonoidHom.range (mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)

-- INSTANCE (free from Core): :

class IsArithmetic (𝒢 : Subgroup (GL (Fin 2) ℝ)) : Prop where
  is_commensurable : Commensurable 𝒢 𝒮ℒ

-- INSTANCE (free from Core): :

lemma isArithmetic_iff_finiteIndex {Γ : Subgroup SL(2, ℤ)} : IsArithmetic Γ ↔ Γ.FiniteIndex := by
  constructor <;>
  · refine fun ⟨h⟩ ↦ ⟨?_⟩
    simpa [Commensurable, MonoidHom.range_eq_map, ← relIndex_comap,
      comap_map_eq_self_of_injective mapGL_injective] using h

-- INSTANCE (free from Core): (Γ

-- INSTANCE (free from Core): IsArithmetic.finiteIndex_comap

-- INSTANCE (free from Core): {Γ

-- INSTANCE (free from Core): IsArithmetic.isFiniteRelIndexSL

-- INSTANCE (free from Core): IsArithmetic.inter

end SL2Z_in_GL2R

end Subgroup

namespace Matrix.SpecialLinearGroup

-- INSTANCE (free from Core): discreteSpecialLinearGroupIntRange

lemma isClosedEmbedding_mapGLInt : Topology.IsClosedEmbedding (mapGL ℝ : SL n ℤ → GL n ℝ) :=
  ⟨isEmbedding_mapGL (Isometry.isEmbedding fun _ _ ↦ rfl), (mapGL ℝ).range.isClosed_of_discrete⟩

end Matrix.SpecialLinearGroup

-- INSTANCE (free from Core): Subgroup.IsArithmetic.discreteTopology

section adjoinNeg

variable {R : Type*} [Ring R]

def Subgroup.adjoinNegOne (𝒢 : Subgroup (GL n R)) : Subgroup (GL n R) where
  carrier := {g | g ∈ 𝒢 ∨ -g ∈ 𝒢}
  mul_mem' ha hb := by
    rcases ha with ha | ha <;>
      rcases hb with hb | hb <;>
      · have := mul_mem ha hb
        aesop
  one_mem' := by simp
  inv_mem' ha := by
    rcases ha with (ha | ha) <;>
    · have := inv_mem ha
      aesop
