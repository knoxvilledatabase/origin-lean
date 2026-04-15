/-
Extracted from MeasureTheory/Function/SpecialFunctions/Inner.lean
Genuine: 6 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

/-!
# Measurability of scalar products
-/

variable {α : Type*} {𝕜 : Type*} {E : Type*}

variable [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

@[aesop safe 20 apply (rule_sets := [Measurable])]
theorem Measurable.inner {_ : MeasurableSpace α} [MeasurableSpace E] [OpensMeasurableSpace E]
    [SecondCountableTopology E] {f g : α → E} (hf : Measurable f)
    (hg : Measurable g) : Measurable fun t => ⟪f t, g t⟫ :=
  Continuous.measurable2 continuous_inner hf hg

@[measurability]
theorem Measurable.const_inner {_ : MeasurableSpace α} [MeasurableSpace E] [OpensMeasurableSpace E]
    [SecondCountableTopology E] {c : E} {f : α → E} (hf : Measurable f) :
    Measurable fun t => ⟪c, f t⟫ :=
  Measurable.inner measurable_const hf

@[measurability]
theorem Measurable.inner_const {_ : MeasurableSpace α} [MeasurableSpace E] [OpensMeasurableSpace E]
    [SecondCountableTopology E] {c : E} {f : α → E} (hf : Measurable f) :
    Measurable fun t => ⟪f t, c⟫ :=
  Measurable.inner hf measurable_const

@[aesop safe 20 apply (rule_sets := [Measurable])]
theorem AEMeasurable.inner {m : MeasurableSpace α} [MeasurableSpace E] [OpensMeasurableSpace E]
    [SecondCountableTopology E] {μ : MeasureTheory.Measure α} {f g : α → E}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) : AEMeasurable (fun x => ⟪f x, g x⟫) μ := by
  refine ⟨fun x => ⟪hf.mk f x, hg.mk g x⟫, hf.measurable_mk.inner hg.measurable_mk, ?_⟩
  refine hf.ae_eq_mk.mp (hg.ae_eq_mk.mono fun x hxg hxf => ?_)
  dsimp only
  congr

set_option linter.unusedVariables false in

@[measurability]
theorem AEMeasurable.const_inner {m : MeasurableSpace α} [MeasurableSpace E]
    [OpensMeasurableSpace E] [SecondCountableTopology E]
    {μ : MeasureTheory.Measure α} {f : α → E} {c : E} (hf : AEMeasurable f μ) :
    AEMeasurable (fun x => ⟪c, f x⟫) μ :=
  AEMeasurable.inner aemeasurable_const hf

set_option linter.unusedVariables false in

@[measurability]
theorem AEMeasurable.inner_const {m : MeasurableSpace α} [MeasurableSpace E]
    [OpensMeasurableSpace E] [SecondCountableTopology E]
    {μ : MeasureTheory.Measure α} {f : α → E} {c : E} (hf : AEMeasurable f μ) :
    AEMeasurable (fun x => ⟪f x, c⟫) μ :=
  AEMeasurable.inner hf aemeasurable_const
