/-
Extracted from MeasureTheory/Integral/IntervalIntegral/Basic.lean
Genuine: 16 of 16 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Integral over an interval

In this file we define `∫ x in a..b, f x ∂μ` to be `∫ x in Ioc a b, f x ∂μ` if `a ≤ b` and
`-∫ x in Ioc b a, f x ∂μ` if `b ≤ a`.

## Implementation notes

### Avoiding `if`, `min`, and `max`

In order to avoid `if`s in the definition, we define `IntervalIntegrable f μ a b` as
`IntegrableOn f (Ioc a b) μ ∧ IntegrableOn f (Ioc b a) μ`. For any `a`, `b` one of these
intervals is empty and the other coincides with `Set.uIoc a b = Set.Ioc (min a b) (max a b)`.

Similarly, we define `∫ x in a..b, f x ∂μ` to be `∫ x in Ioc a b, f x ∂μ - ∫ x in Ioc b a, f x ∂μ`.
Again, for any `a`, `b` one of these integrals is zero, and the other gives the expected result.

This way some properties can be translated from integrals over sets without dealing with
the cases `a ≤ b` and `b ≤ a` separately.

### Choice of the interval

We use integral over `Set.uIoc a b = Set.Ioc (min a b) (max a b)` instead of one of the other
three possible intervals with the same endpoints for two reasons:

* this way `∫ x in a..b, f x ∂μ + ∫ x in b..c, f x ∂μ = ∫ x in a..c, f x ∂μ` holds whenever
  `f` is integrable on each interval; in particular, it works even if the measure `μ` has an atom
  at `b`; this rules out `Set.Ioo` and `Set.Icc` intervals;
* with this definition for a probability measure `μ`, the integral `∫ x in a..b, 1 ∂μ` equals
  the difference $F_μ(b)-F_μ(a)$, where $F_μ(a)=μ(-∞, a]$ is the
  [cumulative distribution function](https://en.wikipedia.org/wiki/Cumulative_distribution_function)
  of `μ`.

## Tags

integral
-/

noncomputable section

open MeasureTheory Set Filter Function TopologicalSpace

open scoped Topology Filter ENNReal Interval NNReal

variable {ι 𝕜 ε ε' E F A : Type*} [NormedAddCommGroup E]
  [TopologicalSpace ε] [ENormedAddMonoid ε] [TopologicalSpace ε'] [ENormedAddMonoid ε']

/-!
### Integrability on an interval
-/

def IntervalIntegrable (f : ℝ → ε) (μ : Measure ℝ) (a b : ℝ) : Prop :=
  IntegrableOn f (Ioc a b) μ ∧ IntegrableOn f (Ioc b a) μ

/-!
## Basic iff's for `IntervalIntegrable`
-/

variable [PseudoMetrizableSpace ε] {f : ℝ → ε} {a b : ℝ} {μ : Measure ℝ}

theorem intervalIntegrable_iff : IntervalIntegrable f μ a b ↔ IntegrableOn f (Ι a b) μ := by
  rw [uIoc_eq_union, integrableOn_union, IntervalIntegrable]

theorem IntervalIntegrable.def' (h : IntervalIntegrable f μ a b) : IntegrableOn f (Ι a b) μ :=
  intervalIntegrable_iff.mp h

theorem intervalIntegrable_congr_ae {g : ℝ → ε} (h : f =ᵐ[μ.restrict (Ι a b)] g) :
    IntervalIntegrable f μ a b ↔ IntervalIntegrable g μ a b := by
  rw [intervalIntegrable_iff, integrableOn_congr_fun_ae h, intervalIntegrable_iff]

theorem IntervalIntegrable.congr_ae {g : ℝ → ε} (hf : IntervalIntegrable f μ a b)
    (h : f =ᵐ[μ.restrict (Ι a b)] g) :
    IntervalIntegrable g μ a b := by
  rwa [← intervalIntegrable_congr_ae h]

theorem intervalIntegrable_congr {g : ℝ → ε} (h : EqOn f g (Ι a b)) :
    IntervalIntegrable f μ a b ↔ IntervalIntegrable g μ a b :=
  intervalIntegrable_congr_ae <| (ae_restrict_mem measurableSet_uIoc).mono h

alias ⟨IntervalIntegrable.congr, _⟩ := intervalIntegrable_congr

theorem IntervalIntegrable.congr_codiscreteWithin {g : ℝ → ε} [NoAtoms μ]
    (h : f =ᶠ[codiscreteWithin (Ι a b)] g) (hf : IntervalIntegrable f μ a b) :
    IntervalIntegrable g μ a b :=
  hf.congr_ae (ae_restrict_le_codiscreteWithin measurableSet_Ioc h)

theorem intervalIntegrable_congr_codiscreteWithin {g : ℝ → ε} [NoAtoms μ]
    (h : f =ᶠ[codiscreteWithin (Ι a b)] g) :
    IntervalIntegrable f μ a b ↔ IntervalIntegrable g μ a b :=
  ⟨(IntervalIntegrable.congr_codiscreteWithin h ·),
    (IntervalIntegrable.congr_codiscreteWithin h.symm ·)⟩

theorem intervalIntegrable_iff_integrableOn_Ioc_of_le (hab : a ≤ b) :
    IntervalIntegrable f μ a b ↔ IntegrableOn f (Ioc a b) μ := by
  rw [intervalIntegrable_iff, uIoc_of_le hab]

theorem intervalIntegrable_iff' [NoAtoms μ] (h : ‖f (min a b)‖ₑ ≠ ∞ := by finiteness) :
    IntervalIntegrable f μ a b ↔ IntegrableOn f (uIcc a b) μ := by
  rw [intervalIntegrable_iff, ← Icc_min_max, uIoc, integrableOn_Icc_iff_integrableOn_Ioc h]

theorem intervalIntegrable_iff_integrableOn_Icc_of_le [NoAtoms μ]
    (hab : a ≤ b) (ha : ‖f a‖ₑ ≠ ∞ := by finiteness) :
    IntervalIntegrable f μ a b ↔ IntegrableOn f (Icc a b) μ := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab, integrableOn_Icc_iff_integrableOn_Ioc ha]

theorem intervalIntegrable_iff_integrableOn_Ico_of_le [NoAtoms μ]
    (hab : a ≤ b) (ha : ‖f a‖ₑ ≠ ∞ := by finiteness) (hb : ‖f b‖ₑ ≠ ∞ := by finiteness) :
    IntervalIntegrable f μ a b ↔ IntegrableOn f (Ico a b) μ := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab ha,
    integrableOn_Icc_iff_integrableOn_Ico hb]

theorem intervalIntegrable_iff_integrableOn_Ioo_of_le [NoAtoms μ]
    (hab : a ≤ b) (ha : ‖f a‖ₑ ≠ ∞ := by finiteness) (hb : ‖f b‖ₑ ≠ ∞ := by finiteness) :
    IntervalIntegrable f μ a b ↔ IntegrableOn f (Ioo a b) μ := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab ha,
    integrableOn_Icc_iff_integrableOn_Ioo ha hb]

omit [PseudoMetrizableSpace ε] in

theorem MeasureTheory.Integrable.intervalIntegrable (hf : Integrable f μ) :
    IntervalIntegrable f μ a b :=
  ⟨hf.integrableOn, hf.integrableOn⟩

omit [PseudoMetrizableSpace ε] in

theorem MeasureTheory.IntegrableOn.intervalIntegrable (hf : IntegrableOn f [[a, b]] μ) :
    IntervalIntegrable f μ a b :=
  ⟨hf.mono_set (Ioc_subset_Icc_self.trans Icc_subset_uIcc),
    hf.mono_set (Ioc_subset_Icc_self.trans Icc_subset_uIcc')⟩

theorem intervalIntegrable_const_iff {c : ε} (hc : ‖c‖ₑ ≠ ⊤ := by finiteness) :
    IntervalIntegrable (fun _ => c) μ a b ↔ c = 0 ∨ μ (Ι a b) < ∞ := by
  simp [intervalIntegrable_iff, integrableOn_const_iff hc]
