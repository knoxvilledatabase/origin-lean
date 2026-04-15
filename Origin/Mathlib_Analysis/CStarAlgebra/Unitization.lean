/-
Extracted from Analysis/CStarAlgebra/Unitization.lean
Genuine: 4 of 8 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-! # The minimal unitization of a C⋆-algebra

This file shows that when `E` is a C⋆-algebra (over a densely normed field `𝕜`), that the minimal
`Unitization` is as well. In order to ensure that the norm structure is available, we must first
show that every C⋆-algebra is a `RegularNormedAlgebra`.

In addition, we show that in a `RegularNormedAlgebra` which is a `StarRing` for which the
involution is isometric, that multiplication on the right is also an isometry (i.e.,
`Isometry (ContinuousLinearMap.mul 𝕜 E).flip`).
-/

open ContinuousLinearMap

local postfix:max "⋆" => star

variable (𝕜 : Type*) {E : Type*}

namespace ContinuousLinearMap

variable [NontriviallyNormedField 𝕜] [NonUnitalNormedRing E] [StarRing E] [NormedStarGroup E]

variable [NormedSpace 𝕜 E] [IsScalarTower 𝕜 E E] [SMulCommClass 𝕜 E E] [RegularNormedAlgebra 𝕜 E]

lemma opNorm_mul_flip_apply (a : E) : ‖(mul 𝕜 E).flip a‖ = ‖a‖ := by
  refine le_antisymm
    (opNorm_le_bound _ (norm_nonneg _) fun b => by simpa only [mul_comm] using norm_mul_le b a) ?_
  suffices ‖mul 𝕜 E (star a)‖ ≤ ‖(mul 𝕜 E).flip a‖ by
    simpa only [ge_iff_le, opNorm_mul_apply, norm_star] using this
  refine opNorm_le_bound _ (norm_nonneg _) fun b => ?_
  calc ‖mul 𝕜 E (star a) b‖ = ‖(mul 𝕜 E).flip a (star b)‖ := by
        simpa only [mul_apply', flip_apply, star_mul, star_star] using norm_star (star b * a)
    _ ≤ ‖(mul 𝕜 E).flip a‖ * ‖b‖ := by
        simpa only [flip_apply, mul_apply', norm_star] using le_opNorm ((mul 𝕜 E).flip a) (star b)

lemma opNNNorm_mul_flip_apply (a : E) : ‖(mul 𝕜 E).flip a‖₊ = ‖a‖₊ :=
  Subtype.ext (opNorm_mul_flip_apply 𝕜 a)

variable (E)

lemma isometry_mul_flip : Isometry (mul 𝕜 E).flip :=
  AddMonoidHomClass.isometry_of_norm _ (opNorm_mul_flip_apply 𝕜)

end ContinuousLinearMap

variable [DenselyNormedField 𝕜] [NonUnitalNormedRing E] [StarRing E] [CStarRing E]

variable [NormedSpace 𝕜 E] [IsScalarTower 𝕜 E E] [SMulCommClass 𝕜 E E]

variable (E)

-- INSTANCE (free from Core): CStarRing.instRegularNormedAlgebra

section CStarProperty

variable [StarRing 𝕜] [StarModule 𝕜 E]

variable {E}

theorem Unitization.norm_splitMul_snd_sq (x : Unitization 𝕜 E) :
    ‖(Unitization.splitMul 𝕜 E x).snd‖ ^ 2 ≤ ‖(Unitization.splitMul 𝕜 E (star x * x)).snd‖ := by
  /- The key idea is that we can use `sSup_unitClosedBall_eq_norm` to make this about
  applying this linear map to elements of norm at most one. There is a bit of `sqrt` and `sq`
  shuffling that needs to occur, which is primarily just an annoyance. -/
  refine (Real.le_sqrt (norm_nonneg _) (norm_nonneg _)).mp ?_
  simp only [Unitization.splitMul_apply]
  rw [← sSup_unitClosedBall_eq_norm]
  refine csSup_le ((Metric.nonempty_closedBall.2 zero_le_one).image _) ?_
  rintro - ⟨b, hb, rfl⟩
  simp only
  -- rewrite to a more convenient form; this is where we use the C⋆-property
  rw [← Real.sqrt_sq (norm_nonneg _), Real.sqrt_le_sqrt_iff (norm_nonneg _), sq,
    ← CStarRing.norm_star_mul_self, ContinuousLinearMap.add_apply, star_add, mul_apply',
    Algebra.algebraMap_eq_smul_one, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply, star_mul, star_smul, add_mul, smul_mul_assoc, ← mul_smul_comm,
    mul_assoc, ← mul_add, ← sSup_unitClosedBall_eq_norm]
  refine (norm_mul_le _ _).trans ?_
  calc
    _ ≤ ‖star x.fst • (x.fst • b + x.snd * b) + star x.snd * (x.fst • b + x.snd * b)‖ := by
      nth_rewrite 2 [← one_mul ‖_ + _‖]
      gcongr
      exact (norm_star b).symm ▸ mem_closedBall_zero_iff.1 hb
    _ ≤ sSup (_ '' Metric.closedBall 0 1) := le_csSup ?_ ⟨b, hb, ?_⟩
  -- now we just check the side conditions for `le_csSup`. There is nothing of interest here.
  · refine ⟨‖(star x * x).fst‖ + ‖(star x * x).snd‖, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    refine (norm_add_le _ _).trans ?_
    gcongr
    · rw [Algebra.algebraMap_eq_smul_one]
      refine (norm_smul _ _).trans_le ?_
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.1 hy) (norm_nonneg (star x * x).fst)
    · exact (unit_le_opNorm _ y <| mem_closedBall_zero_iff.1 hy).trans (opNorm_mul_apply_le _ _ _)
  · simp only [ContinuousLinearMap.add_apply, mul_apply', Unitization.snd_star, Unitization.snd_mul,
      Unitization.fst_mul, Unitization.fst_star, Algebra.algebraMap_eq_smul_one, smul_apply,
      one_apply, smul_add, mul_add, add_mul]
    simp only [smul_smul, smul_mul_assoc, ← add_assoc, ← mul_assoc, mul_smul_comm]

variable {𝕜}

variable [CStarRing 𝕜]

-- INSTANCE (free from Core): Unitization.instCStarRing

scoped[CStarAlgebra] postfix:max "⁺¹" => Unitization ℂ

-- INSTANCE (free from Core): Unitization.instCStarAlgebra

-- INSTANCE (free from Core): Unitization.instCommCStarAlgebra

end CStarProperty
