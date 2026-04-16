/-
Extracted from Analysis/NormedSpace/Extend.lean
Genuine: 9 | Conflates: 0 | Dissolved: 0 | Infrastructure: 5
-/
import Origin.Core
import Mathlib.Algebra.Algebra.RestrictScalars
import Mathlib.Analysis.NormedSpace.OperatorNorm.Basic
import Mathlib.Analysis.RCLike.Basic

noncomputable section

/-!
# Extending a continuous `ℝ`-linear map to a continuous `𝕜`-linear map

In this file we provide a way to extend a continuous `ℝ`-linear map to a continuous `𝕜`-linear map
in a way that bounds the norm by the norm of the original map, when `𝕜` is either `ℝ` (the
extension is trivial) or `ℂ`. We formulate the extension uniformly, by assuming `RCLike 𝕜`.

We motivate the form of the extension as follows. Note that `fc : F →ₗ[𝕜] 𝕜` is determined fully by
`re fc`: for all `x : F`, `fc (I • x) = I * fc x`, so `im (fc x) = -re (fc (I • x))`. Therefore,
given an `fr : F →ₗ[ℝ] ℝ`, we define `fc x = fr x - fr (I • x) * I`.

## Main definitions

* `LinearMap.extendTo𝕜`
* `ContinuousLinearMap.extendTo𝕜`

## Implementation details

For convenience, the main definitions above operate in terms of `RestrictScalars ℝ 𝕜 F`.
Alternate forms which operate on `[IsScalarTower ℝ 𝕜 F]` instead are provided with a primed name.

-/

open RCLike

open ComplexConjugate

variable {𝕜 : Type*} [RCLike 𝕜] {F : Type*}

namespace LinearMap

variable [AddCommGroup F] [Module ℝ F] [Module 𝕜 F] [IsScalarTower ℝ 𝕜 F]

noncomputable def extendTo𝕜' (fr : F →ₗ[ℝ] ℝ) : F →ₗ[𝕜] 𝕜 := by
  let fc : F → 𝕜 := fun x => (fr x : 𝕜) - (I : 𝕜) * fr ((I : 𝕜) • x)
  have add : ∀ x y : F, fc (x + y) = fc x + fc y := by
    intro x y
    simp only [fc, smul_add, LinearMap.map_add, ofReal_add]
    rw [mul_add]
    abel
  have A : ∀ (c : ℝ) (x : F), (fr ((c : 𝕜) • x) : 𝕜) = (c : 𝕜) * (fr x : 𝕜) := by
    intro c x
    rw [← ofReal_mul]
    congr 1
    rw [RCLike.ofReal_alg, smul_assoc, fr.map_smul, Algebra.id.smul_eq_mul, one_smul]
  have smul_ℝ : ∀ (c : ℝ) (x : F), fc ((c : 𝕜) • x) = (c : 𝕜) * fc x := by
    intro c x
    dsimp only [fc]
    rw [A c x, smul_smul, mul_comm I (c : 𝕜), ← smul_smul, A, mul_sub]
    ring
  have smul_I : ∀ x : F, fc ((I : 𝕜) • x) = (I : 𝕜) * fc x := by
    intro x
    dsimp only [fc]
    cases' @I_mul_I_ax 𝕜 _ with h h
    · simp [h]
    rw [mul_sub, ← mul_assoc, smul_smul, h]
    simp only [neg_mul, LinearMap.map_neg, one_mul, one_smul, mul_neg, ofReal_neg, neg_smul,
      sub_neg_eq_add, add_comm]
  have smul_𝕜 : ∀ (c : 𝕜) (x : F), fc (c • x) = c • fc x := by
    intro c x
    rw [← re_add_im c, add_smul, add_smul, add, smul_ℝ, ← smul_smul, smul_ℝ, smul_I, ← mul_assoc]
    rfl
  exact
    { toFun := fc
      map_add' := add
      map_smul' := smul_𝕜 }

theorem extendTo𝕜'_apply (fr : F →ₗ[ℝ] ℝ) (x : F) :
    fr.extendTo𝕜' x = (fr x : 𝕜) - (I : 𝕜) * (fr ((I : 𝕜) • x) : 𝕜) := rfl

@[simp]
theorem extendTo𝕜'_apply_re (fr : F →ₗ[ℝ] ℝ) (x : F) : re (fr.extendTo𝕜' x : 𝕜) = fr x := by
  simp only [extendTo𝕜'_apply, map_sub, zero_mul, mul_zero, sub_zero,
    rclike_simps]

theorem norm_extendTo𝕜'_apply_sq (fr : F →ₗ[ℝ] ℝ) (x : F) :
    ‖(fr.extendTo𝕜' x : 𝕜)‖ ^ 2 = fr (conj (fr.extendTo𝕜' x : 𝕜) • x) :=
  calc
    ‖(fr.extendTo𝕜' x : 𝕜)‖ ^ 2 = re (conj (fr.extendTo𝕜' x) * fr.extendTo𝕜' x : 𝕜) := by
      rw [RCLike.conj_mul, ← ofReal_pow, ofReal_re]
    _ = fr (conj (fr.extendTo𝕜' x : 𝕜) • x) := by
      rw [← smul_eq_mul, ← map_smul, extendTo𝕜'_apply_re]

end LinearMap

variable [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

namespace ContinuousLinearMap

variable [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F]

theorem norm_extendTo𝕜'_bound (fr : F →L[ℝ] ℝ) (x : F) :
    ‖(fr.toLinearMap.extendTo𝕜' x : 𝕜)‖ ≤ ‖fr‖ * ‖x‖ := by
  set lm : F →ₗ[𝕜] 𝕜 := fr.toLinearMap.extendTo𝕜'
  by_cases h : lm x = 0
  · rw [h, norm_zero]
    apply mul_nonneg <;> exact norm_nonneg _
  rw [← mul_le_mul_left (norm_pos_iff.2 h), ← sq]
  calc
    ‖lm x‖ ^ 2 = fr (conj (lm x : 𝕜) • x) := fr.toLinearMap.norm_extendTo𝕜'_apply_sq x
    _ ≤ ‖fr (conj (lm x : 𝕜) • x)‖ := le_abs_self _
    _ ≤ ‖fr‖ * ‖conj (lm x : 𝕜) • x‖ := le_opNorm _ _
    _ = ‖(lm x : 𝕜)‖ * (‖fr‖ * ‖x‖) := by rw [norm_smul, norm_conj, mul_left_comm]

noncomputable def extendTo𝕜' (fr : F →L[ℝ] ℝ) : F →L[𝕜] 𝕜 :=
  LinearMap.mkContinuous _ ‖fr‖ fr.norm_extendTo𝕜'_bound

theorem extendTo𝕜'_apply (fr : F →L[ℝ] ℝ) (x : F) :
    fr.extendTo𝕜' x = (fr x : 𝕜) - (I : 𝕜) * (fr ((I : 𝕜) • x) : 𝕜) := rfl

@[simp]
theorem norm_extendTo𝕜' (fr : F →L[ℝ] ℝ) : ‖(fr.extendTo𝕜' : F →L[𝕜] 𝕜)‖ = ‖fr‖ :=
  le_antisymm (LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _) <|
    opNorm_le_bound _ (norm_nonneg _) fun x =>
      calc
        ‖fr x‖ = ‖re (fr.extendTo𝕜' x : 𝕜)‖ := congr_arg norm (fr.extendTo𝕜'_apply_re x).symm
        _ ≤ ‖(fr.extendTo𝕜' x : 𝕜)‖ := abs_re_le_norm _
        _ ≤ ‖(fr.extendTo𝕜' : F →L[𝕜] 𝕜)‖ * ‖x‖ := le_opNorm _ _

end ContinuousLinearMap

instance : NormedSpace 𝕜 (RestrictScalars ℝ 𝕜 F) := by
  unfold RestrictScalars
  infer_instance

noncomputable def LinearMap.extendTo𝕜 (fr : RestrictScalars ℝ 𝕜 F →ₗ[ℝ] ℝ) : F →ₗ[𝕜] 𝕜 :=
  fr.extendTo𝕜'

noncomputable def ContinuousLinearMap.extendTo𝕜 (fr : RestrictScalars ℝ 𝕜 F →L[ℝ] ℝ) : F →L[𝕜] 𝕜 :=
  fr.extendTo𝕜'

@[simp]
theorem ContinuousLinearMap.norm_extendTo𝕜 (fr : RestrictScalars ℝ 𝕜 F →L[ℝ] ℝ) :
    ‖fr.extendTo𝕜‖ = ‖fr‖ :=
  fr.norm_extendTo𝕜'
