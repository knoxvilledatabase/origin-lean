/-
Extracted from NumberTheory/NumberField/Units/Basic.lean
Genuine: 6 of 12 | Dissolved: 1 | Infrastructure: 5
-/
import Origin.Core

/-!
# Units of a number field

We prove some basic results on the group `(𝓞 K)ˣ` of units of the ring of integers `𝓞 K` of a number
field `K` and its torsion subgroup.

## Main definition

* `NumberField.Units.torsion`: the torsion subgroup of a number field.

## Main results

* `NumberField.isUnit_iff_norm`: an algebraic integer `x : 𝓞 K` is a unit if and only if
  `|norm ℚ x| = 1`.

* `NumberField.Units.mem_torsion`: a unit `x : (𝓞 K)ˣ` is torsion iff `w x = 1` for all infinite
  places `w` of `K`.

## Tags
number field, units
-/

open scoped NumberField

noncomputable section

open NumberField Units

section Rat

set_option backward.isDefEq.respectTransparency false in

theorem Rat.RingOfIntegers.isUnit_iff {x : 𝓞 ℚ} : IsUnit x ↔ (x : ℚ) = 1 ∨ (x : ℚ) = -1 := by
  simp_rw [(isUnit_map_iff (Rat.ringOfIntegersEquiv : 𝓞 ℚ →+* ℤ) x).symm, Int.isUnit_iff,
    RingEquiv.coe_toRingHom, RingEquiv.map_eq_one_iff, RingEquiv.map_eq_neg_one_iff, ←
    Subtype.coe_injective.eq_iff]; rfl

end Rat

variable (K : Type*) [Field K]

section IsUnit

variable {K}

theorem NumberField.isUnit_iff_norm [NumberField K] {x : 𝓞 K} :
    IsUnit x ↔ |(RingOfIntegers.norm ℚ x : ℚ)| = 1 := by
  convert (RingOfIntegers.isUnit_norm ℚ (F := K)).symm
  rw [← abs_one, abs_eq_abs, ← Rat.RingOfIntegers.isUnit_iff]

end IsUnit

namespace NumberField.Units

section coe

-- INSTANCE (free from Core): :

theorem coe_injective : Function.Injective ((↑) : (𝓞 K)ˣ → K) :=
  RingOfIntegers.coe_injective.comp Units.val_injective

variable {K}

theorem coe_pow (x : (𝓞 K)ˣ) (n : ℕ) : ((x ^ n : (𝓞 K)ˣ) : K) = (x : K) ^ n := by
  rw [← map_pow, ← val_pow_eq_pow_val]

theorem coe_zpow (x : (𝓞 K)ˣ) (n : ℤ) : (↑(x ^ n) : K) = (x : K) ^ n := by
  change ((Units.coeHom K).comp (map (algebraMap (𝓞 K) K))) (x ^ n) = _
  exact map_zpow _ x n

-- DISSOLVED: coe_ne_zero

end coe

variable {K}

protected def complexEmbedding (φ : K →+* ℂ) : (𝓞 K)ˣ →* ℂˣ :=
  (map φ).comp (map (algebraMap (𝓞 K) K).toMonoidHom)
