/-
Extracted from RingTheory/OreLocalization/Ring.lean
Genuine: 4 of 7 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!

# Module and Ring instances of Ore Localizations

The `Monoid` and `DistribMulAction` instances and additive versions are provided in
`Mathlib/RingTheory/OreLocalization/Basic.lean`.

-/

assert_not_exists Subgroup

universe u

namespace OreLocalization

section Module

variable {R : Type*} [Semiring R] {S : Submonoid R} [OreSet S]

variable {X : Type*} [AddCommMonoid X] [Module R X]

protected theorem zero_smul (x : X[S⁻¹]) : (0 : R[S⁻¹]) • x = 0 := by
  induction x with | _ r s
  rw [OreLocalization.zero_def, oreDiv_smul_char 0 r 1 s 0 1 (by simp)]; simp

protected theorem add_smul (y z : R[S⁻¹]) (x : X[S⁻¹]) :
    (y + z) • x = y • x + z • x := by
  induction x with | _ r₁ s₁
  induction y with | _ r₂ s₂
  induction z with | _ r₃ s₃
  rcases oreDivAddChar' r₂ r₃ s₂ s₃ with ⟨ra, sa, ha, q⟩
  rw [q]
  clear q
  rw [OreLocalization.expand' r₂ s₂ sa]
  rcases oreDivSMulChar' (sa • r₂) r₁ (sa * s₂) s₁ with ⟨rb, sb, hb, q⟩
  rw [q]
  clear q
  have hs₃rasb : sb * ra * s₃ ∈ S := by
    rw [mul_assoc, ← ha]
    norm_cast
    apply SetLike.coe_mem
  rw [OreLocalization.expand _ _ _ hs₃rasb]
  have ha' : ↑((sb * sa) * s₂) = sb * ra * s₃ := by simp [ha, mul_assoc]
  rw [← Subtype.coe_eq_of_eq_mk ha']
  rcases oreDivSMulChar' ((sb * ra) • r₃) r₁ (sb * sa * s₂) s₁ with ⟨rc, sc, hc, hc'⟩
  rw [hc']
  rw [oreDiv_add_char _ _ 1 sc (by simp [mul_assoc])]
  rw [OreLocalization.expand' (sa • r₂ + ra • r₃) (sa * s₂) (sc * sb)]
  simp only [smul_eq_mul, one_smul, Submonoid.smul_def, mul_add, Submonoid.coe_mul] at hb hc ⊢
  rw [mul_assoc, hb, mul_assoc, ← mul_assoc _ ra, hc, ← mul_assoc, ← add_mul]
  rw [OreLocalization.smul_cancel']
  simp only [add_smul, ← mul_assoc, smul_smul]

end Module

section Semiring

variable {R : Type*} [Semiring R] {S : Submonoid R} [OreSet S]

attribute [local instance] OreLocalization.oreEqv

protected theorem left_distrib (x y z : R[S⁻¹]) : x * (y + z) = x * y + x * z :=
  OreLocalization.smul_add _ _ _

theorem right_distrib (x y z : R[S⁻¹]) : (x + y) * z = x * z + y * z :=
  OreLocalization.add_smul _ _ _

-- INSTANCE (free from Core): :

variable {X : Type*} [AddCommMonoid X] [Module R X]

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): {R₀}
