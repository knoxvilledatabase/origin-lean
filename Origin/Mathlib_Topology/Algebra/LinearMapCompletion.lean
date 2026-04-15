/-
Extracted from Topology/Algebra/LinearMapCompletion.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Completion of continuous (semi-)linear maps:

This file has a declaration that enables a continuous (semi-)linear map between modules to be
lifted to a continuous semilinear map between the completions of those modules.

## Main declarations:

* `ContinuousLinearMap.completion`: promotes a continuous semilinear map
  from `G` to `H` to a continuous semilinear map from `Completion G` to `Completion H`.
-/

namespace ContinuousLinearMap

open UniformSpace Completion

variable {α β : Type*} {R₁ R₂ : Type*} [UniformSpace α] [AddCommGroup α] [IsUniformAddGroup α]
  [Semiring R₁] [Module R₁ α] [UniformContinuousConstSMul R₁ α] [Semiring R₂] [UniformSpace β]
  [AddCommGroup β] [IsUniformAddGroup β] [Module R₂ β] [UniformContinuousConstSMul R₂ β]
  {σ : R₁ →+* R₂}

noncomputable def completion (f : α →SL[σ] β) : Completion α →SL[σ] Completion β where
  __ := f.toAddMonoidHom.completion f.continuous
  map_smul' r x := by
    induction x using induction_on with
    | hp =>
      exact isClosed_eq (continuous_map.comp <| continuous_const_smul r)
        (continuous_map.const_smul _)
    | ih x => simp [← Completion.coe_smul]
  cont := continuous_map
