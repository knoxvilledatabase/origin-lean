/-
Extracted from Dynamics/Ergodic/Ergodic.lean
Genuine: 13 of 15 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core
import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-!
# Ergodic maps and measures

Let `f : α → α` be measure preserving with respect to a measure `μ`. We say `f` is ergodic with
respect to `μ` (or `μ` is ergodic with respect to `f`) if the only measurable sets `s` such that
`f⁻¹' s = s` are either almost empty or full.

In this file we define ergodic maps / measures together with quasi-ergodic maps / measures and
provide some basic API. Quasi-ergodicity is a weaker condition than ergodicity for which the measure
preserving condition is relaxed to quasi measure preserving.

# Main definitions:

 * `PreErgodic`: the ergodicity condition without the measure preserving condition. This exists
   to share code between the `Ergodic` and `QuasiErgodic` definitions.
 * `Ergodic`: the definition of ergodic maps / measures.
 * `QuasiErgodic`: the definition of quasi ergodic maps / measures.
 * `Ergodic.quasiErgodic`: an ergodic map / measure is quasi ergodic.
 * `QuasiErgodic.ae_empty_or_univ'`: when the map is quasi measure preserving, one may relax the
   strict invariance condition to almost invariance in the ergodicity condition.

-/

open Set Function Filter MeasureTheory MeasureTheory.Measure

open ENNReal

variable {α : Type*} {m : MeasurableSpace α} {s : Set α}

structure PreErgodic (f : α → α) (μ : Measure α := by volume_tac) : Prop where
  aeconst_set ⦃s⦄ : MeasurableSet s → f ⁻¹' s = s → EventuallyConst s (ae μ)

structure Ergodic (f : α → α) (μ : Measure α := by volume_tac) extends
  MeasurePreserving f μ μ, PreErgodic f μ : Prop

structure QuasiErgodic (f : α → α) (μ : Measure α := by volume_tac) extends
  QuasiMeasurePreserving f μ μ, PreErgodic f μ : Prop

variable {f : α → α} {μ : Measure α}

namespace PreErgodic

theorem ae_empty_or_univ (hf : PreErgodic f μ) (hs : MeasurableSet s) (hfs : f ⁻¹' s = s) :
    s =ᵐ[μ] (∅ : Set α) ∨ s =ᵐ[μ] univ := by
  simpa only [eventuallyConst_set'] using hf.aeconst_set hs hfs

theorem measure_self_or_compl_eq_zero (hf : PreErgodic f μ) (hs : MeasurableSet s)
    (hs' : f ⁻¹' s = s) : μ s = 0 ∨ μ sᶜ = 0 := by
  simpa using hf.ae_empty_or_univ hs hs'

theorem ae_mem_or_ae_nmem (hf : PreErgodic f μ) (hsm : MeasurableSet s) (hs : f ⁻¹' s = s) :
    (∀ᵐ x ∂μ, x ∈ s) ∨ ∀ᵐ x ∂μ, x ∉ s :=
  eventuallyConst_set.1 <| hf.aeconst_set hsm hs

theorem prob_eq_zero_or_one [IsProbabilityMeasure μ] (hf : PreErgodic f μ) (hs : MeasurableSet s)
    (hs' : f ⁻¹' s = s) : μ s = 0 ∨ μ s = 1 := by
  simpa [hs] using hf.measure_self_or_compl_eq_zero hs hs'

theorem of_iterate (n : ℕ) (hf : PreErgodic f^[n] μ) : PreErgodic f μ :=
  ⟨fun _ hs hs' => hf.aeconst_set hs <| IsFixedPt.preimage_iterate hs' n⟩

theorem smul_measure {R : Type*} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
    (hf : PreErgodic f μ) (c : R) : PreErgodic f (c • μ) where
  aeconst_set _s hs hfs := (hf.aeconst_set hs hfs).anti <| ae_smul_measure_le _

end PreErgodic

namespace MeasureTheory.MeasurePreserving

variable {β : Type*} {m' : MeasurableSpace β} {μ' : Measure β} {g : α → β}

theorem preErgodic_of_preErgodic_conjugate (hg : MeasurePreserving g μ μ') (hf : PreErgodic f μ)
    {f' : β → β} (h_comm : Semiconj g f f') : PreErgodic f' μ' where
  aeconst_set s hs₀ hs₁ := by
    rw [← hg.aeconst_preimage hs₀.nullMeasurableSet]
    apply hf.aeconst_set (hg.measurable hs₀)
    rw [← preimage_comp, h_comm.comp_eq, preimage_comp, hs₁]

theorem preErgodic_conjugate_iff {e : α ≃ᵐ β} (h : MeasurePreserving e μ μ') :
    PreErgodic (e ∘ f ∘ e.symm) μ' ↔ PreErgodic f μ := by
  refine ⟨fun hf => preErgodic_of_preErgodic_conjugate (h.symm e) hf ?_,
      fun hf => preErgodic_of_preErgodic_conjugate h hf ?_⟩
  · simp [Semiconj]
  · simp [Semiconj]

end MeasureTheory.MeasurePreserving

namespace QuasiErgodic

theorem aeconst_set₀ (hf : QuasiErgodic f μ) (hsm : NullMeasurableSet s μ) (hs : f ⁻¹' s =ᵐ[μ] s) :
    EventuallyConst s (ae μ) :=
  let ⟨_t, h₀, h₁, h₂⟩ := hf.toQuasiMeasurePreserving.exists_preimage_eq_of_preimage_ae hsm hs
  (hf.aeconst_set h₀ h₂).congr h₁

theorem ae_empty_or_univ₀ (hf : QuasiErgodic f μ) (hsm : NullMeasurableSet s μ)
    (hs : f ⁻¹' s =ᵐ[μ] s) :
    s =ᵐ[μ] (∅ : Set α) ∨ s =ᵐ[μ] univ :=
  eventuallyConst_set'.mp <| hf.aeconst_set₀ hsm hs
