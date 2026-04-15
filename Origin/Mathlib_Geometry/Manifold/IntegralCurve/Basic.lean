/-
Extracted from Geometry/Manifold/IntegralCurve/Basic.lean
Genuine: 21 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Geometry.Manifold.MFDeriv.Tangent

/-!
# Integral curves of vector fields on a manifold

Let `M` be a manifold and `v : (x : M) → TangentSpace I x` be a vector field on `M`. An integral
curve of `v` is a function `γ : ℝ → M` such that the derivative of `γ` at `t` equals `v (γ t)`. The
integral curve may only be defined for all `t` within some subset of `ℝ`.

This is the first of a series of files, organised as follows:
* `Mathlib.Geometry.Manifold.IntegralCurve.Basic` (this file): Basic definitions and lemmas relating
them to each other and to continuity and differentiability
* `Mathlib.Geometry.Manifold.IntegralCurve.Transform`: Lemmas about translating or scaling the
domain of an integral curve by a constant
* `Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique`: Local existence and uniqueness theorems for
integral curves

## Main definitions

Let `v : M → TM` be a vector field on `M`, and let `γ : ℝ → M`.
* `IsIntegralCurve γ v`: `γ t` is tangent to `v (γ t)` for all `t : ℝ`. That is, `γ` is a global
integral curve of `v`.
* `IsIntegralCurveOn γ v s`: `γ t` is tangent to `v (γ t)` for all `t ∈ s`, where `s : Set ℝ`.
* `IsIntegralCurveAt γ v t₀`: `γ t` is tangent to `v (γ t)` for all `t` in some open interval
around `t₀`. That is, `γ` is a local integral curve of `v`.

For `IsIntegralCurveOn γ v s` and `IsIntegralCurveAt γ v t₀`, even though `γ` is defined for all
time, its value outside of the set `s` or a small interval around `t₀` is irrelevant and considered
junk.

## Reference

* [Lee, J. M. (2012). _Introduction to Smooth Manifolds_. Springer New York.][lee2012]

## Tags

integral curve, vector field
-/

open scoped Manifold Topology

open Set

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

def IsIntegralCurveOn (γ : ℝ → M) (v : (x : M) → TangentSpace I x) (s : Set ℝ) : Prop :=
  ∀ t ∈ s, HasMFDerivAt 𝓘(ℝ, ℝ) I γ t ((1 : ℝ →L[ℝ] ℝ).smulRight <| v (γ t))

def IsIntegralCurveAt (γ : ℝ → M) (v : (x : M) → TangentSpace I x) (t₀ : ℝ) : Prop :=
  ∀ᶠ t in 𝓝 t₀, HasMFDerivAt 𝓘(ℝ, ℝ) I γ t ((1 : ℝ →L[ℝ] ℝ).smulRight <| v (γ t))

def IsIntegralCurve (γ : ℝ → M) (v : (x : M) → TangentSpace I x) : Prop :=
  ∀ t : ℝ, HasMFDerivAt 𝓘(ℝ, ℝ) I γ t ((1 : ℝ →L[ℝ] ℝ).smulRight (v (γ t)))

variable {γ γ' : ℝ → M} {v : (x : M) → TangentSpace I x} {s s' : Set ℝ} {t₀ : ℝ}

lemma IsIntegralCurve.isIntegralCurveOn (h : IsIntegralCurve γ v) (s : Set ℝ) :
    IsIntegralCurveOn γ v s := fun t _ ↦ h t

lemma isIntegralCurve_iff_isIntegralCurveOn : IsIntegralCurve γ v ↔ IsIntegralCurveOn γ v univ :=
  ⟨fun h ↦ h.isIntegralCurveOn _, fun h t ↦ h t (mem_univ _)⟩

lemma isIntegralCurveAt_iff :
    IsIntegralCurveAt γ v t₀ ↔ ∃ s ∈ 𝓝 t₀, IsIntegralCurveOn γ v s := by
  simp_rw [IsIntegralCurveOn, ← Filter.eventually_iff_exists_mem, IsIntegralCurveAt]

lemma isIntegralCurveAt_iff' :
    IsIntegralCurveAt γ v t₀ ↔ ∃ ε > 0, IsIntegralCurveOn γ v (Metric.ball t₀ ε) := by
  simp_rw [IsIntegralCurveOn, ← Metric.eventually_nhds_iff_ball, IsIntegralCurveAt]

lemma IsIntegralCurve.isIntegralCurveAt (h : IsIntegralCurve γ v) (t : ℝ) :
    IsIntegralCurveAt γ v t := isIntegralCurveAt_iff.mpr ⟨univ, Filter.univ_mem, fun t _ ↦ h t⟩

lemma isIntegralCurve_iff_isIntegralCurveAt :
    IsIntegralCurve γ v ↔ ∀ t : ℝ, IsIntegralCurveAt γ v t :=
  ⟨fun h ↦ h.isIntegralCurveAt, fun h t ↦ by
    obtain ⟨s, hs, h⟩ := isIntegralCurveAt_iff.mp (h t)
    exact h t (mem_of_mem_nhds hs)⟩

lemma IsIntegralCurveOn.mono (h : IsIntegralCurveOn γ v s) (hs : s' ⊆ s) :
    IsIntegralCurveOn γ v s' := fun t ht ↦ h t (mem_of_mem_of_subset ht hs)

lemma IsIntegralCurveOn.of_union (h : IsIntegralCurveOn γ v s) (h' : IsIntegralCurveOn γ v s') :
    IsIntegralCurveOn γ v (s ∪ s') := fun _ ↦ fun | .inl ht => h _ ht | .inr ht => h' _ ht

lemma IsIntegralCurveAt.hasMFDerivAt (h : IsIntegralCurveAt γ v t₀) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I γ t₀ ((1 : ℝ →L[ℝ] ℝ).smulRight (v (γ t₀))) :=
  have ⟨_, hs, h⟩ := isIntegralCurveAt_iff.mp h
  h t₀ (mem_of_mem_nhds hs)

lemma IsIntegralCurveOn.isIntegralCurveAt (h : IsIntegralCurveOn γ v s) (hs : s ∈ 𝓝 t₀) :
    IsIntegralCurveAt γ v t₀ := isIntegralCurveAt_iff.mpr ⟨s, hs, h⟩

lemma IsIntegralCurveAt.isIntegralCurveOn (h : ∀ t ∈ s, IsIntegralCurveAt γ v t) :
    IsIntegralCurveOn γ v s := by
  intros t ht
  obtain ⟨s, hs, h⟩ := isIntegralCurveAt_iff.mp (h t ht)
  exact h t (mem_of_mem_nhds hs)

lemma isIntegralCurveOn_iff_isIntegralCurveAt (hs : IsOpen s) :
    IsIntegralCurveOn γ v s ↔ ∀ t ∈ s, IsIntegralCurveAt γ v t :=
  ⟨fun h _ ht ↦ h.isIntegralCurveAt (hs.mem_nhds ht), IsIntegralCurveAt.isIntegralCurveOn⟩

lemma IsIntegralCurveOn.continuousAt (hγ : IsIntegralCurveOn γ v s) (ht : t₀ ∈ s) :
    ContinuousAt γ t₀ := (hγ t₀ ht).1

lemma IsIntegralCurveOn.continuousOn (hγ : IsIntegralCurveOn γ v s) :
    ContinuousOn γ s := fun t ht ↦ (hγ t ht).1.continuousWithinAt

lemma IsIntegralCurveAt.continuousAt (hγ : IsIntegralCurveAt γ v t₀) :
    ContinuousAt γ t₀ :=
  have ⟨_, hs, hγ⟩ := isIntegralCurveAt_iff.mp hγ
  hγ.continuousAt <| mem_of_mem_nhds hs

lemma IsIntegralCurve.continuous (hγ : IsIntegralCurve γ v) : Continuous γ :=
  continuous_iff_continuousAt.mpr fun _ ↦ (hγ.isIntegralCurveOn univ).continuousAt (mem_univ _)

variable [SmoothManifoldWithCorners I M]

lemma IsIntegralCurveOn.hasDerivAt (hγ : IsIntegralCurveOn γ v s) {t : ℝ} (ht : t ∈ s)
    (hsrc : γ t ∈ (extChartAt I (γ t₀)).source) :
    HasDerivAt ((extChartAt I (γ t₀)) ∘ γ)
      (tangentCoordChange I (γ t) (γ t₀) (γ t) (v (γ t))) t := by
  -- turn `HasDerivAt` into comp of `HasMFDerivAt`
  have hsrc := extChartAt_source I (γ t₀) ▸ hsrc
  rw [hasDerivAt_iff_hasFDerivAt, ← hasMFDerivAt_iff_hasFDerivAt]
  apply (HasMFDerivAt.comp t
    (hasMFDerivAt_extChartAt (I := I) hsrc) (hγ _ ht)).congr_mfderiv
  rw [ContinuousLinearMap.ext_iff]
  intro a
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, map_smul,
    ← ContinuousLinearMap.one_apply (R₁ := ℝ) a, ← ContinuousLinearMap.smulRight_apply,
    mfderiv_chartAt_eq_tangentCoordChange hsrc]
  rfl

lemma IsIntegralCurveAt.eventually_hasDerivAt (hγ : IsIntegralCurveAt γ v t₀) :
    ∀ᶠ t in 𝓝 t₀, HasDerivAt ((extChartAt I (γ t₀)) ∘ γ)
      (tangentCoordChange I (γ t) (γ t₀) (γ t) (v (γ t))) t := by
  apply eventually_mem_nhds_iff.mpr
    (hγ.continuousAt.preimage_mem_nhds (extChartAt_source_mem_nhds (I := I) _)) |>.and hγ |>.mono
  rintro t ⟨ht1, ht2⟩
  have hsrc := mem_of_mem_nhds ht1
  rw [mem_preimage, extChartAt_source I (γ t₀)] at hsrc
  rw [hasDerivAt_iff_hasFDerivAt, ← hasMFDerivAt_iff_hasFDerivAt]
  apply (HasMFDerivAt.comp t (hasMFDerivAt_extChartAt (I := I) hsrc) ht2).congr_mfderiv
  rw [ContinuousLinearMap.ext_iff]
  intro a
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, map_smul,
    ← ContinuousLinearMap.one_apply (R₁ := ℝ) a, ← ContinuousLinearMap.smulRight_apply,
    mfderiv_chartAt_eq_tangentCoordChange hsrc]
  rfl
