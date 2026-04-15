/-
Extracted from Analysis/Normed/Operator/Extend.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Extension of continuous linear maps on Banach spaces

In this file we provide two different ways to extend a continuous linear map defined on a dense
subspace to the entire Banach space.

* `ContinuousLinearMap.extend`: Extend `f : E →SL[σ₁₂] F` to a continuous linear map
  `Eₗ →SL[σ₁₂] F`, where `e : E →ₗ[𝕜] Eₗ` is a dense map that is `IsUniformInducing`.
* `LinearMap.extendOfNorm`: Extend `f : E →ₛₗ[σ₁₂] F` to a continuous linear map
  `Eₗ →SL[σ₁₂] F`, where `e : E →ₗ[𝕜] Eₗ` is a dense map and we have the norm estimate
  `‖f x‖ ≤ C * ‖e x‖` for all `x : E`.

Moreover, we can extend a linear equivalence:
* `LinearEquiv.extend`: Extend a linear equivalence between normed spaces to a continuous linear
  equivalence between Banach spaces with two dense maps `e₁` and `e₂` and the corresponding norm
  estimates.
* `LinearEquiv.extendOfIsometry`: Extend `f : E ≃ₗ[𝕜] F` to a linear isometry equivalence
  `Eₗ →ₗᵢ[𝕜] Fₗ`, where `e₁ : E →ₗ[𝕜] Eₗ` and `e₂ : F →ₗ[𝕜] Fₗ` are dense maps into Banach spaces
  and `f` preserves the norm.

-/

suppress_compilation

open scoped NNReal

variable {𝕜 𝕜₂ E Eₗ F Fₗ : Type*}

namespace ContinuousLinearMap

section Extend

section Ring

variable [AddCommGroup E] [UniformSpace E] [IsUniformAddGroup E]
  [AddCommGroup F] [UniformSpace F] [IsUniformAddGroup F] [T0Space F]
  [AddCommMonoid Eₗ] [UniformSpace Eₗ] [ContinuousAdd Eₗ]
  [Semiring 𝕜] [Semiring 𝕜₂] [Module 𝕜 E] [Module 𝕜₂ F] [Module 𝕜 Eₗ]
  [ContinuousConstSMul 𝕜 Eₗ] [ContinuousConstSMul 𝕜₂ F]
  {σ₁₂ : 𝕜 →+* 𝕜₂} (f g : E →SL[σ₁₂] F) [CompleteSpace F] (e : E →L[𝕜] Eₗ)

open scoped Classical in

def extend : Eₗ →SL[σ₁₂] F :=
  if h : DenseRange e ∧ IsUniformInducing e then
  -- extension of `f` is continuous
  have cont := (uniformContinuous_uniformly_extend h.2 h.1 f.uniformContinuous).continuous
  -- extension of `f` agrees with `f` on the domain of the embedding `e`
  have eq := uniformly_extend_of_ind h.2 h.1 f.uniformContinuous
  { toFun := (h.2.isDenseInducing h.1).extend f
    map_add' := by
      refine h.1.induction_on₂ ?_ ?_
      · exact isClosed_eq (cont.comp continuous_add)
          ((cont.comp continuous_fst).add (cont.comp continuous_snd))
      · intro x y
        simp only [eq, ← e.map_add]
        exact f.map_add _ _
    map_smul' := fun k => by
      refine fun b => h.1.induction_on b ?_ ?_
      · exact isClosed_eq (cont.comp (continuous_const_smul _))
          ((continuous_const_smul _).comp cont)
      · intro x
        rw [← map_smul]
        simp only [eq]
        exact map_smulₛₗ _ _ _
    cont }
  else 0

variable {e}
