/-
Extracted from Analysis/ODE/Transform.lean
Genuine: 15 of 19 | Dissolved: 4 | Infrastructure: 0
-/
import Origin.Core

/-!
# Translation and scaling of integral curves

New integral curves may be constructed by translating or scaling the domain of an existing integral
curve.

## Tags

integral curve, vector field
-/

open Function Set Pointwise

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {γ γ' : ℝ → E} {v : ℝ → E → E} {s s' : Set ℝ} {t₀ : ℝ}

/-! ### Translation lemmas -/

section Translation

lemma IsIntegralCurveOn.comp_add (hγ : IsIntegralCurveOn γ v s) (dt : ℝ) :
    IsIntegralCurveOn (γ ∘ (· + dt)) (v ∘ (· + dt)) (-dt +ᵥ s) := by
  intros t ht
  rw [comp_apply, hasDerivWithinAt_iff_hasFDerivWithinAt, Function.comp_def,
    hasFDerivWithinAt_comp_add_right, ← hasDerivWithinAt_iff_hasFDerivWithinAt, vadd_neg_vadd]
  apply hγ (t + dt)
  rwa [mem_vadd_set_iff_neg_vadd_mem, neg_neg, vadd_eq_add, add_comm] at ht

lemma isIntegralCurveOn_comp_add {dt : ℝ} :
    IsIntegralCurveOn (γ ∘ (· + dt)) (v ∘ (· + dt)) (-dt +ᵥ s) ↔ IsIntegralCurveOn γ v s := by
  refine ⟨fun hγ ↦ ?_, fun hγ ↦ hγ.comp_add _⟩
  convert hγ.comp_add (-dt)
  · ext t
    simp only [comp_apply, neg_add_cancel_right]
  · ext t
    simp only [comp_apply, neg_add_cancel_right]
  · simp only [neg_neg, vadd_neg_vadd]

lemma isIntegralCurveOn_comp_sub {dt : ℝ} :
    IsIntegralCurveOn (γ ∘ (· - dt)) (v ∘ (· - dt)) (dt +ᵥ s) ↔ IsIntegralCurveOn γ v s := by
  simpa using isIntegralCurveOn_comp_add (dt := -dt)

lemma IsIntegralCurveOn.comp_sub (hγ : IsIntegralCurveOn γ v s) (dt : ℝ) :
    IsIntegralCurveOn (γ ∘ (· - dt)) (v ∘ (· - dt)) (dt +ᵥ s) :=
  isIntegralCurveOn_comp_sub.mpr hγ

lemma isIntegralCurveAt_comp_add {dt : ℝ} :
    IsIntegralCurveAt (γ ∘ (· + dt)) (v ∘ (· + dt)) (t₀ - dt) ↔ IsIntegralCurveAt γ v t₀ := by
  simp_rw [isIntegralCurveAt_iff_exists_pos]
  congrm ∃ ε > 0, ?_
  convert isIntegralCurveOn_comp_add
  simp [neg_add_eq_sub]

lemma IsIntegralCurveAt.comp_add (hγ : IsIntegralCurveAt γ v t₀) (dt : ℝ) :
    IsIntegralCurveAt (γ ∘ (· + dt)) (v ∘ (· + dt)) (t₀ - dt) :=
  isIntegralCurveAt_comp_add.mpr hγ

lemma isIntegralCurveAt_comp_sub {dt : ℝ} :
   IsIntegralCurveAt (γ ∘ (· - dt)) (v ∘ (· - dt)) (t₀ + dt) ↔ IsIntegralCurveAt γ v t₀ := by
  simpa using isIntegralCurveAt_comp_add (dt := -dt)

lemma IsIntegralCurveAt.comp_sub (hγ : IsIntegralCurveAt γ v t₀) (dt : ℝ) :
    IsIntegralCurveAt (γ ∘ (· - dt)) (v ∘ (· - dt)) (t₀ + dt) :=
  isIntegralCurveAt_comp_sub.mpr hγ

lemma IsIntegralCurve.comp_add (hγ : IsIntegralCurve γ v) (dt : ℝ) :
    IsIntegralCurve (γ ∘ (· + dt)) (v ∘ (· + dt)) := by
  rw [← isIntegralCurveOn_univ] at *
  simpa using hγ.comp_add dt

lemma isIntegralCurve_comp_add {dt : ℝ} :
    IsIntegralCurve (γ ∘ (· + dt)) (v ∘ (· + dt)) ↔ IsIntegralCurve γ v := by
  simp_rw [← isIntegralCurveOn_univ]
  convert isIntegralCurveOn_comp_add
  simp

lemma isIntegralCurve_comp_sub {dt : ℝ} :
    IsIntegralCurve (γ ∘ (· - dt)) (v ∘ (· - dt)) ↔ IsIntegralCurve γ v := by
  simpa using isIntegralCurve_comp_add (dt := -dt)

lemma IsIntegralCurve.comp_sub (hγ : IsIntegralCurve γ v) (dt : ℝ) :
    IsIntegralCurve (γ ∘ (· - dt)) (v ∘ (· - dt)) :=
  isIntegralCurve_comp_sub.mpr hγ

end Translation

/-! ### Scaling lemmas -/

section Scaling

lemma IsIntegralCurveOn.comp_mul (hγ : IsIntegralCurveOn γ v s) (a : ℝ) :
    IsIntegralCurveOn (γ ∘ (· * a)) (a • v ∘ (· * a)) { t | t * a ∈ s } := fun t ht ↦ by
  simp only [comp_apply, Pi.smul_apply]
  exact HasDerivWithinAt.scomp t (hγ (t * a) ht) (hasDerivAt_mul_const a).hasDerivWithinAt
    fun _ ht' ↦ ht'

-- DISSOLVED: isIntegralCurveOn_comp_mul_ne_zero

-- DISSOLVED: IsIntegralCurveAt.comp_mul_ne_zero

-- DISSOLVED: isIntegralCurveAt_comp_mul_ne_zero

lemma IsIntegralCurve.comp_mul (hγ : IsIntegralCurve γ v) (a : ℝ) :
    IsIntegralCurve (γ ∘ (· * a)) (a • v ∘ (· * a)) := by
  rw [← isIntegralCurveOn_univ] at *
  exact hγ.comp_mul _

-- DISSOLVED: isIntegralCurve_comp_mul_ne_zero

lemma isIntegralCurve_const {x : E} (h : ∀ t, v t x = 0) : IsIntegralCurve (fun _ ↦ x) v :=
  fun t ↦ (h t) ▸ hasDerivAt_const _ _

end Scaling
