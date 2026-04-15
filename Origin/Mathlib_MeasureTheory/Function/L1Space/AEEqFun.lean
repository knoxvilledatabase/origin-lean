/-
Extracted from MeasureTheory/Function/L1Space/AEEqFun.lean
Genuine: 11 of 11 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# `L¹` space

In this file we establish an API between `Integrable` and the space `L¹` of equivalence
classes of integrable functions, already defined as a special case of `L^p` spaces for `p = 1`.

## Notation

* `α →₁[μ] β` is the type of `L¹` space, where `α` is a `MeasureSpace` and `β` is a
  `NormedAddCommGroup`. `f : α →ₘ β` is a "function" in `L¹`.
  In comments, `[f]` is also used to denote an `L¹` function.

  `₁` can be typed as `\1`.

## Tags

function space, l1

-/

noncomputable section

open EMetric ENNReal Filter MeasureTheory NNReal Set

variable {α β ε ε' : Type*} {m : MeasurableSpace α} {μ ν : Measure α}

variable [NormedAddCommGroup β] [TopologicalSpace ε] [ContinuousENorm ε]
  [TopologicalSpace ε'] [ESeminormedAddMonoid ε']

namespace MeasureTheory

namespace AEEqFun

def Integrable (f : α →ₘ[μ] ε) : Prop :=
  MeasureTheory.Integrable f μ

theorem integrable_mk {f : α → ε} (hf : AEStronglyMeasurable f μ) :
    Integrable (mk f hf : α →ₘ[μ] ε) ↔ MeasureTheory.Integrable f μ := by
  simp only [Integrable]
  apply integrable_congr
  exact coeFn_mk f hf

theorem integrable_coeFn {f : α →ₘ[μ] ε} : MeasureTheory.Integrable f μ ↔ Integrable f := by
  rw [← integrable_mk f.aestronglyMeasurable, mk_coeFn]

theorem integrable_zero : Integrable (0 : α →ₘ[μ] ε') :=
  (MeasureTheory.integrable_zero α ε' μ).congr (coeFn_mk _ _).symm

end

theorem Integrable.neg {f : α →ₘ[μ] β} : Integrable f → Integrable (-f) :=
  induction_on f fun _f hfm hfi => (integrable_mk _).2 ((integrable_mk hfm).1 hfi).neg

theorem integrable_iff_mem_L1 {f : α →ₘ[μ] β} : Integrable f ↔ f ∈ (α →₁[μ] β) := by
  rw [← integrable_coeFn, ← memLp_one_iff_integrable, Lp.mem_Lp_iff_memLp]

theorem Integrable.add {f g : α →ₘ[μ] β} : Integrable f → Integrable g → Integrable (f + g) := by
  refine induction_on₂ f g fun f hf g hg hfi hgi => ?_
  simp only [integrable_mk, mk_add_mk] at hfi hgi ⊢
  exact hfi.add hgi

theorem Integrable.sub {f g : α →ₘ[μ] β} (hf : Integrable f) (hg : Integrable g) :
    Integrable (f - g) :=
  (sub_eq_add_neg f g).symm ▸ hf.add hg.neg

end

section IsBoundedSMul

variable {𝕜 : Type*} [NormedRing 𝕜] [Module 𝕜 β] [IsBoundedSMul 𝕜 β]

theorem Integrable.smul {c : 𝕜} {f : α →ₘ[μ] β} : Integrable f → Integrable (c • f) :=
  induction_on f fun _f hfm hfi => (integrable_mk _).2 <|
    by simpa using ((integrable_mk hfm).1 hfi).smul c

end IsBoundedSMul

end

end AEEqFun

namespace L1

theorem integrable_coeFn (f : α →₁[μ] β) : Integrable f μ := by
  rw [← memLp_one_iff_integrable]
  exact Lp.memLp f

theorem hasFiniteIntegral_coeFn (f : α →₁[μ] β) : HasFiniteIntegral f μ :=
  (integrable_coeFn f).hasFiniteIntegral
