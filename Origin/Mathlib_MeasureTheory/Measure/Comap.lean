/-
Extracted from MeasureTheory/Measure/Comap.lean
Genuine: 13 of 13 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Pullback of a measure

In this file we define the pullback `MeasureTheory.Measure.comap f μ`
of a measure `μ` along an injective map `f`
such that the image of any measurable set under `f` is a null-measurable set.
If `f` does not have these properties, then we define `comap f μ` to be zero.

In the future, we may decide to redefine `comap f μ` so that it gives meaningful results, e.g.,
for covering maps like `(↑) : ℝ → AddCircle (1 : ℝ)`.
-/

open Function Set Filter

open scoped ENNReal

noncomputable section

namespace MeasureTheory

namespace Measure

variable {α β γ : Type*} {s : Set α}

open Classical in

def comapₗ [MeasurableSpace α] [MeasurableSpace β] (f : α → β) : Measure β →ₗ[ℝ≥0∞] Measure α :=
  if hf : Injective f ∧ ∀ s, MeasurableSet s → MeasurableSet (f '' s) then
    liftLinear (OuterMeasure.comap f) fun μ s hs t => by
      simp only [OuterMeasure.comap_apply, image_inter hf.1, image_diff hf.1]
      apply le_toOuterMeasure_caratheodory
      exact hf.2 s hs
  else 0

theorem comapₗ_apply {_ : MeasurableSpace α} {_ : MeasurableSpace β} (f : α → β)
    (hfi : Injective f) (hf : ∀ s, MeasurableSet s → MeasurableSet (f '' s)) (μ : Measure β)
    (hs : MeasurableSet s) : comapₗ f μ s = μ (f '' s) := by
  rw [comapₗ, dif_pos, liftLinear_apply _ hs, OuterMeasure.comap_apply, coe_toOuterMeasure]
  exact ⟨hfi, hf⟩

open Classical in

def comap [MeasurableSpace α] [MeasurableSpace β] (f : α → β) (μ : Measure β) : Measure α :=
  if hf : Injective f ∧ ∀ s, MeasurableSet s → NullMeasurableSet (f '' s) μ then
    (OuterMeasure.comap f μ.toOuterMeasure).toMeasure fun s hs t => by
      simp only [OuterMeasure.comap_apply, image_inter hf.1, image_diff hf.1]
      exact (measure_inter_add_diff₀ _ (hf.2 s hs)).symm
  else 0

variable {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
  {f : α → β} {g : β → γ}

theorem comap_apply₀ (f : α → β) (μ : Measure β) (hfi : Injective f)
    (hf : ∀ s, MeasurableSet s → NullMeasurableSet (f '' s) μ)
    (hs : NullMeasurableSet s (comap f μ)) : comap f μ s = μ (f '' s) := by
  rw [comap, dif_pos (And.intro hfi hf)] at hs ⊢
  rw [toMeasure_apply₀ _ _ hs, OuterMeasure.comap_apply, coe_toOuterMeasure]

lemma comap_undef {μ : Measure β}
    (h : ¬ (Injective f ∧ ∀ s, MeasurableSet s → NullMeasurableSet (f '' s) μ)) :
    comap f μ = 0 := dif_neg h

theorem le_comap_apply (f : α → β) (μ : Measure β) (hfi : Injective f)
    (hf : ∀ s, MeasurableSet s → NullMeasurableSet (f '' s) μ) (s : Set α) :
    μ (f '' s) ≤ comap f μ s := by
  rw [comap, dif_pos (And.intro hfi hf)]
  exact le_toMeasure_apply _ _ _

theorem comap_apply (f : α → β) (hfi : Injective f)
    (hf : ∀ s, MeasurableSet s → MeasurableSet (f '' s)) (μ : Measure β) (hs : MeasurableSet s) :
    comap f μ s = μ (f '' s) :=
  comap_apply₀ f μ hfi (fun s hs => (hf s hs).nullMeasurableSet) hs.nullMeasurableSet

theorem comap_apply_le (f : α → β) (μ : Measure β) (hs : NullMeasurableSet s (μ.comap f)) :
    μ.comap f s ≤ μ (f '' s) := by
  by_cases hf : Injective f ∧ ∀ t, MeasurableSet t → NullMeasurableSet (f '' t) μ
  · rw [comap_apply₀ _ _ hf.1 hf.2 hs]
  · simp [comap_undef hf]

theorem comapₗ_eq_comap (f : α → β) (hfi : Injective f)
    (hf : ∀ s, MeasurableSet s → MeasurableSet (f '' s)) (μ : Measure β) (hs : MeasurableSet s) :
    comapₗ f μ s = comap f μ s :=
  (comapₗ_apply f hfi hf μ hs).trans (comap_apply f hfi hf μ hs).symm

theorem measure_image_eq_zero_of_comap_eq_zero (f : α → β) (μ : Measure β) (hfi : Injective f)
    (hf : ∀ s, MeasurableSet s → NullMeasurableSet (f '' s) μ) {s : Set α} (hs : comap f μ s = 0) :
    μ (f '' s) = 0 :=
  le_antisymm ((le_comap_apply f μ hfi hf s).trans hs.le) (zero_le _)

theorem ae_eq_image_of_ae_eq_comap (f : α → β) (μ : Measure β) (hfi : Injective f)
    (hf : ∀ s, MeasurableSet s → NullMeasurableSet (f '' s) μ)
    {s t : Set α} (hst : s =ᵐ[comap f μ] t) : f '' s =ᵐ[μ] f '' t := by
  rw [EventuallyEq, ae_iff] at hst ⊢
  have h_eq_α : { a : α | ¬s a = t a } = s \ t ∪ t \ s := by
    ext1 x
    simp only [eq_iff_iff, mem_setOf_eq, mem_union, mem_diff]
    tauto
  have h_eq_β : { a : β | ¬(f '' s) a = (f '' t) a } = f '' s \ f '' t ∪ f '' t \ f '' s := by
    ext1 x
    simp only [eq_iff_iff, mem_setOf_eq, mem_union, mem_diff]
    tauto
  rw [← Set.image_diff hfi, ← Set.image_diff hfi, ← Set.image_union] at h_eq_β
  rw [h_eq_β]
  rw [h_eq_α] at hst
  exact measure_image_eq_zero_of_comap_eq_zero f μ hfi hf hst

theorem NullMeasurableSet.image (f : α → β) (μ : Measure β) (hfi : Injective f)
    (hf : ∀ s, MeasurableSet s → NullMeasurableSet (f '' s) μ)
    (hs : NullMeasurableSet s (μ.comap f)) : NullMeasurableSet (f '' s) μ := by
  refine ⟨toMeasurable μ (f '' toMeasurable (μ.comap f) s), measurableSet_toMeasurable _ _, ?_⟩
  refine EventuallyEq.trans ?_ (NullMeasurableSet.toMeasurable_ae_eq ?_).symm
  swap
  · exact hf _ (measurableSet_toMeasurable _ _)
  have h : toMeasurable (comap f μ) s =ᵐ[comap f μ] s :=
    NullMeasurableSet.toMeasurable_ae_eq hs
  exact ae_eq_image_of_ae_eq_comap f μ hfi hf h.symm

theorem comap_preimage (f : α → β) (μ : Measure β) (hf : Injective f) (hf' : Measurable f)
    (h : ∀ t, MeasurableSet t → NullMeasurableSet (f '' t) μ) {s : Set β} (hs : MeasurableSet s) :
    μ.comap f (f ⁻¹' s) = μ (s ∩ range f) := by
  rw [comap_apply₀ _ _ hf h (hf' hs).nullMeasurableSet, image_preimage_eq_inter_range]
