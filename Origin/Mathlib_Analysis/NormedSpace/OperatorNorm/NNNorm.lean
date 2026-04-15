/-
Extracted from Analysis/NormedSpace/OperatorNorm/NNNorm.lean
Genuine: 15 | Conflates: 6 | Dissolved: 1 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Analysis.NormedSpace.OperatorNorm.Basic

/-!
# Operator norm as an `NNNorm`

Operator norm as an `NNNorm`, i.e. taking values in non-negative reals.

-/

open Bornology

open Filter hiding map_smul

open scoped NNReal Topology Uniformity

variable {𝕜 𝕜₂ 𝕜₃ E Eₗ F Fₗ G Gₗ 𝓕 : Type*}

section SemiNormed

open Metric ContinuousLinearMap

variable [SeminormedAddCommGroup E] [SeminormedAddCommGroup Eₗ] [SeminormedAddCommGroup F]
  [SeminormedAddCommGroup Fₗ] [SeminormedAddCommGroup G] [SeminormedAddCommGroup Gₗ]

variable [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] [NontriviallyNormedField 𝕜₃]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜 Eₗ] [NormedSpace 𝕜₂ F] [NormedSpace 𝕜 Fₗ] [NormedSpace 𝕜₃ G]
  [NormedSpace 𝕜 Gₗ] {σ₁₂ : 𝕜 →+* 𝕜₂} {σ₂₃ : 𝕜₂ →+* 𝕜₃} {σ₁₃ : 𝕜 →+* 𝕜₃}
  [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

variable [FunLike 𝓕 E F]

namespace ContinuousLinearMap

section OpNorm

open Set Real

section

variable [RingHomIsometric σ₁₂] [RingHomIsometric σ₂₃] (f g : E →SL[σ₁₂] F) (h : F →SL[σ₂₃] G)
  (x : E)

theorem nnnorm_def (f : E →SL[σ₁₂] F) : ‖f‖₊ = sInf { c | ∀ x, ‖f x‖₊ ≤ c * ‖x‖₊ } := by
  ext
  rw [NNReal.coe_sInf, coe_nnnorm, norm_def, NNReal.coe_image]
  simp_rw [← NNReal.coe_le_coe, NNReal.coe_mul, coe_nnnorm, mem_setOf_eq, NNReal.coe_mk,
    exists_prop]

theorem opNNNorm_le_bound (f : E →SL[σ₁₂] F) (M : ℝ≥0) (hM : ∀ x, ‖f x‖₊ ≤ M * ‖x‖₊) : ‖f‖₊ ≤ M :=
  opNorm_le_bound f (zero_le M) hM

-- DISSOLVED: opNNNorm_le_bound'

theorem opNNNorm_le_of_unit_nnnorm [NormedSpace ℝ E] [NormedSpace ℝ F] {f : E →L[ℝ] F} {C : ℝ≥0}
    (hf : ∀ x, ‖x‖₊ = 1 → ‖f x‖₊ ≤ C) : ‖f‖₊ ≤ C :=
  opNorm_le_of_unit_norm C.coe_nonneg fun x hx => hf x <| by rwa [← NNReal.coe_eq_one]

alias op_nnnorm_le_of_unit_nnnorm := opNNNorm_le_of_unit_nnnorm

theorem opNNNorm_le_of_lipschitz {f : E →SL[σ₁₂] F} {K : ℝ≥0} (hf : LipschitzWith K f) :
    ‖f‖₊ ≤ K :=
  opNorm_le_of_lipschitz hf

theorem opNNNorm_eq_of_bounds {φ : E →SL[σ₁₂] F} (M : ℝ≥0) (h_above : ∀ x, ‖φ x‖₊ ≤ M * ‖x‖₊)
    (h_below : ∀ N, (∀ x, ‖φ x‖₊ ≤ N * ‖x‖₊) → M ≤ N) : ‖φ‖₊ = M :=
  Subtype.ext <| opNorm_eq_of_bounds (zero_le M) h_above <| Subtype.forall'.mpr h_below

theorem opNNNorm_le_iff {f : E →SL[σ₁₂] F} {C : ℝ≥0} : ‖f‖₊ ≤ C ↔ ∀ x, ‖f x‖₊ ≤ C * ‖x‖₊ :=
  opNorm_le_iff C.2

theorem isLeast_opNNNorm : IsLeast {C : ℝ≥0 | ∀ x, ‖f x‖₊ ≤ C * ‖x‖₊} ‖f‖₊ := by
  simpa only [← opNNNorm_le_iff] using isLeast_Ici

theorem opNNNorm_comp_le [RingHomIsometric σ₁₃] (f : E →SL[σ₁₂] F) : ‖h.comp f‖₊ ≤ ‖h‖₊ * ‖f‖₊ :=
  opNorm_comp_le h f

theorem le_opNNNorm : ‖f x‖₊ ≤ ‖f‖₊ * ‖x‖₊ :=
  f.le_opNorm x

theorem nndist_le_opNNNorm (x y : E) : nndist (f x) (f y) ≤ ‖f‖₊ * nndist x y :=
  dist_le_opNorm f x y

theorem lipschitz : LipschitzWith ‖f‖₊ f :=
  AddMonoidHomClass.lipschitz_of_bound_nnnorm f _ f.le_opNNNorm

theorem lipschitz_apply (x : E) : LipschitzWith ‖x‖₊ fun f : E →SL[σ₁₂] F => f x :=
  lipschitzWith_iff_norm_sub_le.2 fun f g => ((f - g).le_opNorm x).trans_eq (mul_comm _ _)

end

section Sup

variable [RingHomIsometric σ₁₂]

theorem exists_mul_lt_apply_of_lt_opNNNorm (f : E →SL[σ₁₂] F) {r : ℝ≥0} (hr : r < ‖f‖₊) :
    ∃ x, r * ‖x‖₊ < ‖f x‖₊ := by
  simpa only [not_forall, not_le, Set.mem_setOf] using
    not_mem_of_lt_csInf (nnnorm_def f ▸ hr : r < sInf { c : ℝ≥0 | ∀ x, ‖f x‖₊ ≤ c * ‖x‖₊ })
      (OrderBot.bddBelow _)

alias exists_mul_lt_apply_of_lt_op_nnnorm := exists_mul_lt_apply_of_lt_opNNNorm

theorem exists_mul_lt_of_lt_opNorm (f : E →SL[σ₁₂] F) {r : ℝ} (hr₀ : 0 ≤ r) (hr : r < ‖f‖) :
    ∃ x, r * ‖x‖ < ‖f x‖ := by
  lift r to ℝ≥0 using hr₀
  exact f.exists_mul_lt_apply_of_lt_opNNNorm hr

alias exists_mul_lt_of_lt_op_norm := exists_mul_lt_of_lt_opNorm

-- CONFLATES (assumes ground = zero): exists_lt_apply_of_lt_opNNNorm
theorem exists_lt_apply_of_lt_opNNNorm {𝕜 𝕜₂ E F : Type*} [NormedAddCommGroup E]
    [SeminormedAddCommGroup F] [DenselyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] {σ₁₂ : 𝕜 →+* 𝕜₂}
    [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] [RingHomIsometric σ₁₂] (f : E →SL[σ₁₂] F) {r : ℝ≥0}
    (hr : r < ‖f‖₊) : ∃ x : E, ‖x‖₊ < 1 ∧ r < ‖f x‖₊ := by
  obtain ⟨y, hy⟩ := f.exists_mul_lt_apply_of_lt_opNNNorm hr
  have hy' : ‖y‖₊ ≠ 0 :=
    nnnorm_ne_zero_iff.2 fun heq => by
      simp [heq, nnnorm_zero, map_zero, not_lt_zero'] at hy
  have hfy : ‖f y‖₊ ≠ 0 := (zero_le'.trans_lt hy).ne'
  rw [← inv_inv ‖f y‖₊, NNReal.lt_inv_iff_mul_lt (inv_ne_zero hfy), mul_assoc, mul_comm ‖y‖₊, ←
    mul_assoc, ← NNReal.lt_inv_iff_mul_lt hy'] at hy
  obtain ⟨k, hk₁, hk₂⟩ := NormedField.exists_lt_nnnorm_lt 𝕜 hy
  refine ⟨k • y, (nnnorm_smul k y).symm ▸ (NNReal.lt_inv_iff_mul_lt hy').1 hk₂, ?_⟩
  have : ‖σ₁₂ k‖₊ = ‖k‖₊ := Subtype.ext RingHomIsometric.is_iso
  rwa [map_smulₛₗ f, nnnorm_smul, ← div_lt_iff₀ hfy.bot_lt, div_eq_mul_inv, this]

alias exists_lt_apply_of_lt_op_nnnorm := exists_lt_apply_of_lt_opNNNorm

-- CONFLATES (assumes ground = zero): exists_lt_apply_of_lt_opNorm
theorem exists_lt_apply_of_lt_opNorm {𝕜 𝕜₂ E F : Type*} [NormedAddCommGroup E]
    [SeminormedAddCommGroup F] [DenselyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] {σ₁₂ : 𝕜 →+* 𝕜₂}
    [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] [RingHomIsometric σ₁₂] (f : E →SL[σ₁₂] F) {r : ℝ}
    (hr : r < ‖f‖) : ∃ x : E, ‖x‖ < 1 ∧ r < ‖f x‖ := by
  by_cases hr₀ : r < 0
  · exact ⟨0, by simpa using hr₀⟩
  · lift r to ℝ≥0 using not_lt.1 hr₀
    exact f.exists_lt_apply_of_lt_opNNNorm hr

alias exists_lt_apply_of_lt_op_norm := exists_lt_apply_of_lt_opNorm

-- CONFLATES (assumes ground = zero): sSup_unit_ball_eq_nnnorm
theorem sSup_unit_ball_eq_nnnorm {𝕜 𝕜₂ E F : Type*} [NormedAddCommGroup E]
    [SeminormedAddCommGroup F] [DenselyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] {σ₁₂ : 𝕜 →+* 𝕜₂}
    [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] [RingHomIsometric σ₁₂] (f : E →SL[σ₁₂] F) :
    sSup ((fun x => ‖f x‖₊) '' ball 0 1) = ‖f‖₊ := by
  refine csSup_eq_of_forall_le_of_forall_lt_exists_gt ((nonempty_ball.mpr zero_lt_one).image _) ?_
    fun ub hub => ?_
  · rintro - ⟨x, hx, rfl⟩
    simpa only [mul_one] using f.le_opNorm_of_le (mem_ball_zero_iff.1 hx).le
  · obtain ⟨x, hx, hxf⟩ := f.exists_lt_apply_of_lt_opNNNorm hub
    exact ⟨_, ⟨x, mem_ball_zero_iff.2 hx, rfl⟩, hxf⟩

-- CONFLATES (assumes ground = zero): sSup_unit_ball_eq_norm
theorem sSup_unit_ball_eq_norm {𝕜 𝕜₂ E F : Type*} [NormedAddCommGroup E] [SeminormedAddCommGroup F]
    [DenselyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] {σ₁₂ : 𝕜 →+* 𝕜₂} [NormedSpace 𝕜 E]
    [NormedSpace 𝕜₂ F] [RingHomIsometric σ₁₂] (f : E →SL[σ₁₂] F) :
    sSup ((fun x => ‖f x‖) '' ball 0 1) = ‖f‖ := by
  simpa only [NNReal.coe_sSup, Set.image_image] using NNReal.coe_inj.2 f.sSup_unit_ball_eq_nnnorm

-- CONFLATES (assumes ground = zero): sSup_closed_unit_ball_eq_nnnorm
theorem sSup_closed_unit_ball_eq_nnnorm {𝕜 𝕜₂ E F : Type*} [NormedAddCommGroup E]
    [SeminormedAddCommGroup F] [DenselyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] {σ₁₂ : 𝕜 →+* 𝕜₂}
    [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] [RingHomIsometric σ₁₂] (f : E →SL[σ₁₂] F) :
    sSup ((fun x => ‖f x‖₊) '' closedBall 0 1) = ‖f‖₊ := by
  have hbdd : ∀ y ∈ (fun x => ‖f x‖₊) '' closedBall 0 1, y ≤ ‖f‖₊ := by
    rintro - ⟨x, hx, rfl⟩
    exact f.unit_le_opNorm x (mem_closedBall_zero_iff.1 hx)
  refine le_antisymm (csSup_le ((nonempty_closedBall.mpr zero_le_one).image _) hbdd) ?_
  rw [← sSup_unit_ball_eq_nnnorm]
  exact csSup_le_csSup ⟨‖f‖₊, hbdd⟩ ((nonempty_ball.2 zero_lt_one).image _)
    (Set.image_subset _ ball_subset_closedBall)

-- CONFLATES (assumes ground = zero): sSup_closed_unit_ball_eq_norm
theorem sSup_closed_unit_ball_eq_norm {𝕜 𝕜₂ E F : Type*} [NormedAddCommGroup E]
    [SeminormedAddCommGroup F] [DenselyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] {σ₁₂ : 𝕜 →+* 𝕜₂}
    [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] [RingHomIsometric σ₁₂] (f : E →SL[σ₁₂] F) :
    sSup ((fun x => ‖f x‖) '' closedBall 0 1) = ‖f‖ := by
  simpa only [NNReal.coe_sSup, Set.image_image] using
    NNReal.coe_inj.2 f.sSup_closed_unit_ball_eq_nnnorm

end Sup

end OpNorm

end ContinuousLinearMap

namespace ContinuousLinearEquiv

variable {σ₂₁ : 𝕜₂ →+* 𝕜} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] [RingHomIsometric σ₁₂]

variable (e : E ≃SL[σ₁₂] F)

protected theorem lipschitz : LipschitzWith ‖(e : E →SL[σ₁₂] F)‖₊ e :=
  (e : E →SL[σ₁₂] F).lipschitz

end ContinuousLinearEquiv

end SemiNormed
