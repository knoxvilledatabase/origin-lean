/-
Extracted from Topology/Algebra/Valued/ValuationTopology.lean
Genuine: 1 of 3 | Dissolved: 2 | Infrastructure: 0
-/
import Origin.Core

/-!
# The topology on a valued ring

In this file, we define the non-Archimedean topology induced by a valuation on a ring.
The main definition is a `Valued` type class which equips a ring with a valuation taking
values in a group with zero. Other instances are then deduced from this.

*NOTE* (2025-07-02):
The `Valued` class defined in this file will eventually get replaced with `ValuativeRel`
from `Mathlib.RingTheory.Valuation.ValuativeRel.Basic`. New developments on valued rings/fields
should take this into consideration.

-/

open scoped Topology uniformity

open MonoidWithZeroHom MonoidWithZeroHom.ValueGroup₀ Set Valuation

noncomputable section

universe v u

variable {R K : Type u} [Ring R] [DivisionRing K] {Γ₀ : Type v} [LinearOrderedCommGroupWithZero Γ₀]

namespace Valuation

variable (v : Valuation R Γ₀)

-- DISSOLVED: map_eq_one_of_forall_lt

set_option backward.isDefEq.respectTransparency false in

theorem subgroups_basis :
    RingSubgroupsBasis fun γ : (ValueGroup₀ v)ˣ ↦
      (v.ltAddSubgroup (Units.map (ValueGroup₀.embedding (f := v)) γ) : AddSubgroup R) :=
  { inter := by
      classical
      rintro γ₀ γ₁
      use min γ₀ γ₁
      have hmin : embedding (min γ₀.1 γ₁.1) = min (embedding γ₀.1) (embedding γ₁.1) :=
        embedding_strictMono.monotone.map_inf γ₀.1 γ₁.1
      simp [ltAddSubgroup, hmin]
      tauto
    mul := by
      -- Will be fixed by using MonoidWithZeroHom in ValueGroup₀.
      letI : LinearOrderedCommGroupWithZero (ValueGroup₀ v) := --inferInstance failed
        MonoidWithZeroHom.ValueGroup₀.instLinearOrderedCommGroupWithZero
      rintro γ
      obtain ⟨γ₀, h⟩ := exists_square_le γ
      use γ₀
      rintro - ⟨r, r_in, s, s_in, rfl⟩
      simp only [ltAddSubgroup, Units.coe_map, MonoidHom.coe_coe, AddSubgroup.coe_set_mk,
        AddSubmonoid.coe_set_mk, AddSubsemigroup.coe_set_mk, mem_setOf_eq] at r_in s_in
      simp only [coe_ltAddSubgroup, Units.coe_map, MonoidHom.coe_coe, mem_setOf_eq]
      rw [← restrict_lt_iff_lt_embedding] at *
      calc
        v.restrict (r * s) = v.restrict r * v.restrict s := Valuation.map_mul _ _ _
        _ < γ₀.1 * γ₀.1 := by gcongr <;> exact zero_le'
        _ ≤ γ := mod_cast h
    leftMul := by
      rintro x γ
      rcases GroupWithZero.eq_zero_or_unit (v x) with (Hx | ⟨γx, Hx⟩)
      · use (1 : (ValueGroup₀ v)ˣ)
        rintro y _
        simp only [coe_ltAddSubgroup, preimage_setOf_eq, mem_setOf_eq]
        rw [Valuation.map_mul, Hx, zero_mul]
        exact Units.zero_lt _
      · set u : (ValueGroup₀ v)ˣ := Units.mk0 ((restrict₀ v) x)
          (by simp [restrict₀_apply]; aesop) with hu_def
        have hu : ValueGroup₀.embedding u⁻¹.1 = γx⁻¹ := by
          simp [restrict₀_apply, embedding_apply, hu_def, Hx]
        use u⁻¹ * γ
        rintro y (vy_lt : v y < ValueGroup₀.embedding (u⁻¹ * γ).1)
        simp only [coe_ltAddSubgroup, preimage_setOf_eq, mem_setOf_eq]
        rw [Valuation.map_mul, Hx, mul_comm]
        rw [Units.val_mul, mul_comm, map_mul, hu] at vy_lt
        simpa using mul_inv_lt_of_lt_mul₀ vy_lt
    rightMul := by
      rintro x γ
      rcases GroupWithZero.eq_zero_or_unit (v x) with (Hx | ⟨γx, Hx⟩)
      · use 1
        rintro y _
        simp only [coe_ltAddSubgroup, preimage_setOf_eq, mem_setOf_eq, Valuation.map_mul, Hx,
          mul_zero, Units.zero_lt]
      · set u : (ValueGroup₀ v)ˣ := Units.mk0 ((restrict₀ v) x)
          (by simp [restrict₀_apply]; aesop) with hu_def
        have hu : ValueGroup₀.embedding u⁻¹.1 = γx⁻¹ := by simp [restrict₀_apply, embedding_apply,
          hu_def, Hx]
        use u⁻¹ * γ
        rintro y (vy_lt : v y < ValueGroup₀.embedding (u⁻¹ * γ).1)
        simp only [coe_ltAddSubgroup, preimage_setOf_eq, mem_setOf_eq, Valuation.map_mul, Hx]
        rw [Units.val_mul, mul_comm, map_mul, hu] at vy_lt
        simpa using mul_inv_lt_of_lt_mul₀ vy_lt }

end Valuation

-- DISSOLVED: Valued

namespace Valued
