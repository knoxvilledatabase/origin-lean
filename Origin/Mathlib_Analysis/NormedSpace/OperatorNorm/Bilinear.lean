/-
Extracted from Analysis/NormedSpace/OperatorNorm/Bilinear.lean
Genuine: 33 | Conflates: 0 | Dissolved: 0 | Infrastructure: 16
-/
import Origin.Core
import Mathlib.Analysis.NormedSpace.OperatorNorm.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

/-!
# Operator norm: bilinear maps

This file contains lemmas concerning operator norm as applied to bilinear maps `E × F → G`,
interpreted as linear maps `E → F → G` as usual (and similarly for semilinear variants).

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

theorem opNorm_ext [RingHomIsometric σ₁₃] (f : E →SL[σ₁₂] F) (g : E →SL[σ₁₃] G)
    (h : ∀ x, ‖f x‖ = ‖g x‖) : ‖f‖ = ‖g‖ :=
  opNorm_eq_of_bounds (norm_nonneg _)
    (fun x => by
      rw [h x]
      exact le_opNorm _ _)
    fun c hc h₂ =>
    opNorm_le_bound _ hc fun z => by
      rw [← h z]
      exact h₂ z

variable [RingHomIsometric σ₂₃]

theorem opNorm_le_bound₂ (f : E →SL[σ₁₃] F →SL[σ₂₃] G) {C : ℝ} (h0 : 0 ≤ C)
    (hC : ∀ x y, ‖f x y‖ ≤ C * ‖x‖ * ‖y‖) : ‖f‖ ≤ C :=
  f.opNorm_le_bound h0 fun x => (f x).opNorm_le_bound (mul_nonneg h0 (norm_nonneg _)) <| hC x

theorem le_opNorm₂ [RingHomIsometric σ₁₃] (f : E →SL[σ₁₃] F →SL[σ₂₃] G) (x : E) (y : F) :
    ‖f x y‖ ≤ ‖f‖ * ‖x‖ * ‖y‖ :=
  (f x).le_of_opNorm_le (f.le_opNorm x) y

theorem le_of_opNorm₂_le_of_le [RingHomIsometric σ₁₃] (f : E →SL[σ₁₃] F →SL[σ₂₃] G) {x : E} {y : F}
    {a b c : ℝ} (hf : ‖f‖ ≤ a) (hx : ‖x‖ ≤ b) (hy : ‖y‖ ≤ c) :
    ‖f x y‖ ≤ a * b * c :=
  (f x).le_of_opNorm_le_of_le (f.le_of_opNorm_le_of_le hf hx) hy

end OpNorm

end ContinuousLinearMap

namespace LinearMap

lemma norm_mkContinuous₂_aux (f : E →ₛₗ[σ₁₃] F →ₛₗ[σ₂₃] G) (C : ℝ)
    (h : ∀ x y, ‖f x y‖ ≤ C * ‖x‖ * ‖y‖) (x : E) :
    ‖(f x).mkContinuous (C * ‖x‖) (h x)‖ ≤ max C 0 * ‖x‖ :=
  (mkContinuous_norm_le' (f x) (h x)).trans_eq <| by
    rw [max_mul_of_nonneg _ _ (norm_nonneg x), zero_mul]

variable [RingHomIsometric σ₂₃]

def mkContinuousOfExistsBound₂ (f : E →ₛₗ[σ₁₃] F →ₛₗ[σ₂₃] G)
    (h : ∃ C, ∀ x y, ‖f x y‖ ≤ C * ‖x‖ * ‖y‖) : E →SL[σ₁₃] F →SL[σ₂₃] G :=
  LinearMap.mkContinuousOfExistsBound
    { toFun := fun x => (f x).mkContinuousOfExistsBound <| let ⟨C, hC⟩ := h; ⟨C * ‖x‖, hC x⟩
      map_add' := fun x y => by
        ext z
        simp
      map_smul' := fun c x => by
        ext z
        simp } <|
    let ⟨C, hC⟩ := h; ⟨max C 0, norm_mkContinuous₂_aux f C hC⟩

def mkContinuous₂ (f : E →ₛₗ[σ₁₃] F →ₛₗ[σ₂₃] G) (C : ℝ) (hC : ∀ x y, ‖f x y‖ ≤ C * ‖x‖ * ‖y‖) :
    E →SL[σ₁₃] F →SL[σ₂₃] G :=
  mkContinuousOfExistsBound₂ f ⟨C, hC⟩

@[simp]
theorem mkContinuous₂_apply (f : E →ₛₗ[σ₁₃] F →ₛₗ[σ₂₃] G) {C : ℝ}
    (hC : ∀ x y, ‖f x y‖ ≤ C * ‖x‖ * ‖y‖) (x : E) (y : F) : f.mkContinuous₂ C hC x y = f x y :=
  rfl

theorem mkContinuous₂_norm_le' (f : E →ₛₗ[σ₁₃] F →ₛₗ[σ₂₃] G) {C : ℝ}
    (hC : ∀ x y, ‖f x y‖ ≤ C * ‖x‖ * ‖y‖) : ‖f.mkContinuous₂ C hC‖ ≤ max C 0 :=
  mkContinuous_norm_le _ (le_max_iff.2 <| Or.inr le_rfl) (norm_mkContinuous₂_aux f C hC)

theorem mkContinuous₂_norm_le (f : E →ₛₗ[σ₁₃] F →ₛₗ[σ₂₃] G) {C : ℝ} (h0 : 0 ≤ C)
    (hC : ∀ x y, ‖f x y‖ ≤ C * ‖x‖ * ‖y‖) : ‖f.mkContinuous₂ C hC‖ ≤ C :=
  (f.mkContinuous₂_norm_le' hC).trans_eq <| max_eq_left h0

end LinearMap

namespace ContinuousLinearMap

variable [RingHomIsometric σ₂₃] [RingHomIsometric σ₁₃]

def flip (f : E →SL[σ₁₃] F →SL[σ₂₃] G) : F →SL[σ₂₃] E →SL[σ₁₃] G :=
  LinearMap.mkContinuous₂
    -- Porting note: the `simp only`s below used to be `rw`.
    -- Now that doesn't work as we need to do some beta reduction along the way.
    (LinearMap.mk₂'ₛₗ σ₂₃ σ₁₃ (fun y x => f x y) (fun x y z => (f z).map_add x y)
      (fun c y x => (f x).map_smulₛₗ c y) (fun z x y => by simp only [f.map_add, add_apply])
        (fun c y x => by simp only [f.map_smulₛₗ, smul_apply]))
    ‖f‖ fun y x => (f.le_opNorm₂ x y).trans_eq <| by simp only [mul_right_comm]

private theorem le_norm_flip (f : E →SL[σ₁₃] F →SL[σ₂₃] G) : ‖f‖ ≤ ‖flip f‖ :=
  #adaptation_note
  /--
  After https://github.com/leanprover/lean4/pull/4119 we either need
  to specify the `f.flip` argument, or use `set_option maxSynthPendingDepth 2 in`.
  -/
  f.opNorm_le_bound₂ (norm_nonneg f.flip) fun x y => by
    rw [mul_right_comm]
    exact (flip f).le_opNorm₂ y x

@[simp]
theorem flip_apply (f : E →SL[σ₁₃] F →SL[σ₂₃] G) (x : E) (y : F) : f.flip y x = f x y :=
  rfl

@[simp]
theorem flip_flip (f : E →SL[σ₁₃] F →SL[σ₂₃] G) : f.flip.flip = f := by
  ext
  rfl

@[simp]
theorem opNorm_flip (f : E →SL[σ₁₃] F →SL[σ₂₃] G) : ‖f.flip‖ = ‖f‖ :=
  le_antisymm (by simpa only [flip_flip] using le_norm_flip f.flip) (le_norm_flip f)

@[simp]
theorem flip_add (f g : E →SL[σ₁₃] F →SL[σ₂₃] G) : (f + g).flip = f.flip + g.flip :=
  rfl

@[simp]
theorem flip_smul (c : 𝕜₃) (f : E →SL[σ₁₃] F →SL[σ₂₃] G) : (c • f).flip = c • f.flip :=
  rfl

variable (E F G σ₁₃ σ₂₃)

def flipₗᵢ' : (E →SL[σ₁₃] F →SL[σ₂₃] G) ≃ₗᵢ[𝕜₃] F →SL[σ₂₃] E →SL[σ₁₃] G where
  toFun := flip
  invFun := flip
  map_add' := flip_add
  map_smul' := flip_smul
  left_inv := flip_flip
  right_inv := flip_flip
  norm_map' := opNorm_flip

variable {E F G σ₁₃ σ₂₃}

@[simp]
theorem flipₗᵢ'_symm : (flipₗᵢ' E F G σ₂₃ σ₁₃).symm = flipₗᵢ' F E G σ₁₃ σ₂₃ :=
  rfl

@[simp]
theorem coe_flipₗᵢ' : ⇑(flipₗᵢ' E F G σ₂₃ σ₁₃) = flip :=
  rfl

variable (𝕜 E Fₗ Gₗ)

def flipₗᵢ : (E →L[𝕜] Fₗ →L[𝕜] Gₗ) ≃ₗᵢ[𝕜] Fₗ →L[𝕜] E →L[𝕜] Gₗ where
  toFun := flip
  invFun := flip
  map_add' := flip_add
  map_smul' := flip_smul
  left_inv := flip_flip
  right_inv := flip_flip
  norm_map' := opNorm_flip

variable {𝕜 E Fₗ Gₗ}

@[simp]
theorem flipₗᵢ_symm : (flipₗᵢ 𝕜 E Fₗ Gₗ).symm = flipₗᵢ 𝕜 Fₗ E Gₗ :=
  rfl

@[simp]
theorem coe_flipₗᵢ : ⇑(flipₗᵢ 𝕜 E Fₗ Gₗ) = flip :=
  rfl

variable (F σ₁₂)

variable [RingHomIsometric σ₁₂]

def apply' : E →SL[σ₁₂] (E →SL[σ₁₂] F) →L[𝕜₂] F :=
  flip (id 𝕜₂ (E →SL[σ₁₂] F))

variable {F σ₁₂}

@[simp]
theorem apply_apply' (v : E) (f : E →SL[σ₁₂] F) : apply' F σ₁₂ v f = f v :=
  rfl

variable (𝕜 Fₗ)

def apply : E →L[𝕜] (E →L[𝕜] Fₗ) →L[𝕜] Fₗ :=
  flip (id 𝕜 (E →L[𝕜] Fₗ))

variable {𝕜 Fₗ}

@[simp]
theorem apply_apply (v : E) (f : E →L[𝕜] Fₗ) : apply 𝕜 Fₗ v f = f v :=
  rfl

variable (σ₁₂ σ₂₃ E F G)

def compSL : (F →SL[σ₂₃] G) →L[𝕜₃] (E →SL[σ₁₂] F) →SL[σ₂₃] E →SL[σ₁₃] G :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂'ₛₗ (RingHom.id 𝕜₃) σ₂₃ comp add_comp smul_comp comp_add fun c f g => by
      ext
      simp only [ContinuousLinearMap.map_smulₛₗ, coe_smul', coe_comp', Function.comp_apply,
        Pi.smul_apply])
    1 fun f g => by simpa only [one_mul] using opNorm_comp_le f g

set_option maxSynthPendingDepth 2 in

theorem norm_compSL_le : ‖compSL E F G σ₁₂ σ₂₃‖ ≤ 1 :=
  LinearMap.mkContinuous₂_norm_le _ zero_le_one _

variable {σ₁₂ σ₂₃ E F G}

@[simp]
theorem compSL_apply (f : F →SL[σ₂₃] G) (g : E →SL[σ₁₂] F) : compSL E F G σ₁₂ σ₂₃ f g = f.comp g :=
  rfl

theorem _root_.Continuous.const_clm_comp {X} [TopologicalSpace X] {f : X → E →SL[σ₁₂] F}
    (hf : Continuous f) (g : F →SL[σ₂₃] G) :
    Continuous (fun x => g.comp (f x) : X → E →SL[σ₁₃] G) :=
  (compSL E F G σ₁₂ σ₂₃ g).continuous.comp hf

theorem _root_.Continuous.clm_comp_const {X} [TopologicalSpace X] {g : X → F →SL[σ₂₃] G}
    (hg : Continuous g) (f : E →SL[σ₁₂] F) :
    Continuous (fun x => (g x).comp f : X → E →SL[σ₁₃] G) :=
  (@ContinuousLinearMap.flip _ _ _ _ _ (E →SL[σ₁₃] G) _ _ _ _ _ _ _ _ _ _ _ _ _
    (compSL E F G σ₁₂ σ₂₃) f).continuous.comp hg

variable (𝕜 σ₁₂ σ₂₃ E Fₗ Gₗ)

def compL : (Fₗ →L[𝕜] Gₗ) →L[𝕜] (E →L[𝕜] Fₗ) →L[𝕜] E →L[𝕜] Gₗ :=
  compSL E Fₗ Gₗ (RingHom.id 𝕜) (RingHom.id 𝕜)

set_option maxSynthPendingDepth 2 in

theorem norm_compL_le : ‖compL 𝕜 E Fₗ Gₗ‖ ≤ 1 :=
  norm_compSL_le _ _ _ _ _

@[simp]
theorem compL_apply (f : Fₗ →L[𝕜] Gₗ) (g : E →L[𝕜] Fₗ) : compL 𝕜 E Fₗ Gₗ f g = f.comp g :=
  rfl

variable (Eₗ) {𝕜 E Fₗ Gₗ}

@[simps! apply]
def precompR (L : E →L[𝕜] Fₗ →L[𝕜] Gₗ) : E →L[𝕜] (Eₗ →L[𝕜] Fₗ) →L[𝕜] Eₗ →L[𝕜] Gₗ :=
  (compL 𝕜 Eₗ Fₗ Gₗ).comp L

def precompL (L : E →L[𝕜] Fₗ →L[𝕜] Gₗ) : (Eₗ →L[𝕜] E) →L[𝕜] Fₗ →L[𝕜] Eₗ →L[𝕜] Gₗ :=
  (precompR Eₗ (flip L)).flip

@[simp] lemma precompL_apply (L : E →L[𝕜] Fₗ →L[𝕜] Gₗ) (u : Eₗ →L[𝕜] E) (f : Fₗ) (g : Eₗ) :
    precompL Eₗ L u f g = L (u g) f := rfl

set_option maxSynthPendingDepth 2 in

theorem norm_precompR_le (L : E →L[𝕜] Fₗ →L[𝕜] Gₗ) : ‖precompR Eₗ L‖ ≤ ‖L‖ :=
  calc
    ‖precompR Eₗ L‖ ≤ ‖compL 𝕜 Eₗ Fₗ Gₗ‖ * ‖L‖ := opNorm_comp_le _ _
    _ ≤ 1 * ‖L‖ := mul_le_mul_of_nonneg_right (norm_compL_le _ _ _ _) (norm_nonneg L)
    _ = ‖L‖ := by rw [one_mul]

set_option maxSynthPendingDepth 2 in

theorem norm_precompL_le (L : E →L[𝕜] Fₗ →L[𝕜] Gₗ) : ‖precompL Eₗ L‖ ≤ ‖L‖ := by
  rw [precompL, opNorm_flip, ← opNorm_flip L]
  exact norm_precompR_le _ L.flip

end ContinuousLinearMap

variable {σ₂₁ : 𝕜₂ →+* 𝕜} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]

namespace ContinuousLinearMap

variable {E' F' : Type*} [SeminormedAddCommGroup E'] [SeminormedAddCommGroup F']

variable {𝕜₁' : Type*} {𝕜₂' : Type*} [NontriviallyNormedField 𝕜₁'] [NontriviallyNormedField 𝕜₂']
  [NormedSpace 𝕜₁' E'] [NormedSpace 𝕜₂' F'] {σ₁' : 𝕜₁' →+* 𝕜} {σ₁₃' : 𝕜₁' →+* 𝕜₃} {σ₂' : 𝕜₂' →+* 𝕜₂}
  {σ₂₃' : 𝕜₂' →+* 𝕜₃} [RingHomCompTriple σ₁' σ₁₃ σ₁₃'] [RingHomCompTriple σ₂' σ₂₃ σ₂₃']
  [RingHomIsometric σ₂₃] [RingHomIsometric σ₁₃'] [RingHomIsometric σ₂₃']

def bilinearComp (f : E →SL[σ₁₃] F →SL[σ₂₃] G) (gE : E' →SL[σ₁'] E) (gF : F' →SL[σ₂'] F) :
    E' →SL[σ₁₃'] F' →SL[σ₂₃'] G :=
  ((f.comp gE).flip.comp gF).flip

@[simp]
theorem bilinearComp_apply (f : E →SL[σ₁₃] F →SL[σ₂₃] G) (gE : E' →SL[σ₁'] E) (gF : F' →SL[σ₂'] F)
    (x : E') (y : F') : f.bilinearComp gE gF x y = f (gE x) (gF y) :=
  rfl

variable [RingHomIsometric σ₁₃] [RingHomIsometric σ₁'] [RingHomIsometric σ₂']

def deriv₂ (f : E →L[𝕜] Fₗ →L[𝕜] Gₗ) : E × Fₗ →L[𝕜] E × Fₗ →L[𝕜] Gₗ :=
  f.bilinearComp (fst _ _ _) (snd _ _ _) + f.flip.bilinearComp (snd _ _ _) (fst _ _ _)

@[simp]
theorem coe_deriv₂ (f : E →L[𝕜] Fₗ →L[𝕜] Gₗ) (p : E × Fₗ) :
    ⇑(f.deriv₂ p) = fun q : E × Fₗ => f p.1 q.2 + f q.1 p.2 :=
  rfl

theorem map_add_add (f : E →L[𝕜] Fₗ →L[𝕜] Gₗ) (x x' : E) (y y' : Fₗ) :
    f (x + x') (y + y') = f x y + f.deriv₂ (x, y) (x', y') + f x' y' := by
  simp only [map_add, add_apply, coe_deriv₂, add_assoc]
  abel

@[simp]
theorem norm_smulRight_apply (c : E →L[𝕜] 𝕜) (f : Fₗ) : ‖smulRight c f‖ = ‖c‖ * ‖f‖ := by
  refine le_antisymm ?_ ?_
  · refine opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) fun x => ?_
    calc
      ‖c x • f‖ = ‖c x‖ * ‖f‖ := norm_smul _ _
      _ ≤ ‖c‖ * ‖x‖ * ‖f‖ := mul_le_mul_of_nonneg_right (le_opNorm _ _) (norm_nonneg _)
      _ = ‖c‖ * ‖f‖ * ‖x‖ := by ring
  · obtain hf | hf := (norm_nonneg f).eq_or_gt
    · simp [hf]
    · rw [← le_div_iff₀ hf]
      refine opNorm_le_bound _ (div_nonneg (norm_nonneg _) (norm_nonneg f)) fun x => ?_
      rw [div_mul_eq_mul_div, le_div_iff₀ hf]
      calc
        ‖c x‖ * ‖f‖ = ‖c x • f‖ := (norm_smul _ _).symm
        _ = ‖smulRight c f x‖ := rfl
        _ ≤ ‖smulRight c f‖ * ‖x‖ := le_opNorm _ _

@[simp]
theorem nnnorm_smulRight_apply (c : E →L[𝕜] 𝕜) (f : Fₗ) : ‖smulRight c f‖₊ = ‖c‖₊ * ‖f‖₊ :=
  NNReal.eq <| c.norm_smulRight_apply f

variable (𝕜 E Fₗ) in

def smulRightL : (E →L[𝕜] 𝕜) →L[𝕜] Fₗ →L[𝕜] E →L[𝕜] Fₗ :=
  LinearMap.mkContinuous₂
    { toFun := smulRightₗ
      map_add' := fun c₁ c₂ => by
        ext x
        simp only [add_smul, coe_smulRightₗ, add_apply, smulRight_apply, LinearMap.add_apply]
      map_smul' := fun m c => by
        ext x
        dsimp
        rw [smul_smul] }
    1 fun c x => by
      simp only [coe_smulRightₗ, one_mul, norm_smulRight_apply, LinearMap.coe_mk, AddHom.coe_mk,
        le_refl]

@[simp]
theorem norm_smulRightL_apply (c : E →L[𝕜] 𝕜) (f : Fₗ) : ‖smulRightL 𝕜 E Fₗ c f‖ = ‖c‖ * ‖f‖ :=
  norm_smulRight_apply c f

end ContinuousLinearMap

end SemiNormed
