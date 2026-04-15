/-
Extracted from Analysis/SpecialFunctions/Trigonometric/InverseDeriv.lean
Genuine: 8 of 9 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# derivatives of the inverse trigonometric functions

Derivatives of `arcsin` and `arccos`.
-/

noncomputable section

open scoped Topology Filter Real ContDiff

open Set

namespace Real

section Arcsin

theorem deriv_arcsin_aux {x : ℝ} (h₁ : x ≠ -1) (h₂ : x ≠ 1) :
    HasStrictDerivAt arcsin (1 / √(1 - x ^ 2)) x ∧ ContDiffAt ℝ ω arcsin x := by
  rcases h₁.lt_or_gt with h₁ | h₁
  · have : 1 - x ^ 2 < 0 := by nlinarith [h₁]
    rw [sqrt_eq_zero'.2 this.le, div_zero]
    have : arcsin =ᶠ[𝓝 x] fun _ => -(π / 2) :=
      (gt_mem_nhds h₁).mono fun y hy => arcsin_of_le_neg_one hy.le
    exact ⟨(hasStrictDerivAt_const x _).congr_of_eventuallyEq this.symm,
      contDiffAt_const.congr_of_eventuallyEq this⟩
  rcases h₂.lt_or_gt with h₂ | h₂
  · have : 0 < √(1 - x ^ 2) := sqrt_pos.2 (by nlinarith [h₁, h₂])
    simp only [← cos_arcsin, one_div] at this ⊢
    exact ⟨sinPartialHomeomorph.hasStrictDerivAt_symm ⟨h₁, h₂⟩ this.ne' (hasStrictDerivAt_sin _),
      sinPartialHomeomorph.contDiffAt_symm_deriv this.ne' ⟨h₁, h₂⟩ (hasDerivAt_sin _)
        contDiff_sin.contDiffAt⟩
  · have : 1 - x ^ 2 < 0 := by nlinarith [h₂]
    rw [sqrt_eq_zero'.2 this.le, div_zero]
    have : arcsin =ᶠ[𝓝 x] fun _ => π / 2 := (lt_mem_nhds h₂).mono fun y hy => arcsin_of_one_le hy.le
    exact ⟨(hasStrictDerivAt_const x _).congr_of_eventuallyEq this.symm,
      contDiffAt_const.congr_of_eventuallyEq this⟩

theorem hasStrictDerivAt_arcsin {x : ℝ} (h₁ : x ≠ -1) (h₂ : x ≠ 1) :
    HasStrictDerivAt arcsin (1 / √(1 - x ^ 2)) x :=
  (deriv_arcsin_aux h₁ h₂).1

theorem hasDerivAt_arcsin {x : ℝ} (h₁ : x ≠ -1) (h₂ : x ≠ 1) :
    HasDerivAt arcsin (1 / √(1 - x ^ 2)) x :=
  (hasStrictDerivAt_arcsin h₁ h₂).hasDerivAt

theorem contDiffAt_arcsin {x : ℝ} (h₁ : x ≠ -1) (h₂ : x ≠ 1) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n arcsin x :=
  (deriv_arcsin_aux h₁ h₂).2.of_le le_top

theorem hasDerivWithinAt_arcsin_Ici {x : ℝ} (h : x ≠ -1) :
    HasDerivWithinAt arcsin (1 / √(1 - x ^ 2)) (Ici x) x := by
  rcases eq_or_ne x 1 with (rfl | h')
  · convert (hasDerivWithinAt_const (1 : ℝ) _ (π / 2)).congr _ _ <;>
      simp +contextual [arcsin_of_one_le]
  · exact (hasDerivAt_arcsin h h').hasDerivWithinAt

theorem hasDerivWithinAt_arcsin_Iic {x : ℝ} (h : x ≠ 1) :
    HasDerivWithinAt arcsin (1 / √(1 - x ^ 2)) (Iic x) x := by
  rcases em (x = -1) with (rfl | h')
  · convert (hasDerivWithinAt_const (-1 : ℝ) _ (-(π / 2))).congr _ _ <;>
      simp +contextual [arcsin_of_le_neg_one]
  · exact (hasDerivAt_arcsin h' h).hasDerivWithinAt

theorem differentiableWithinAt_arcsin_Iic {x : ℝ} :
    DifferentiableWithinAt ℝ arcsin (Iic x) x ↔ x ≠ 1 := by
  refine ⟨fun h => ?_, fun h => (hasDerivWithinAt_arcsin_Iic h).differentiableWithinAt⟩
  rw [← neg_neg x, ← image_neg_Ici] at h
  have := (h.comp (-x) differentiableWithinAt_id.fun_neg (mapsTo_image _ _)).fun_neg
  simpa [(· ∘ ·), differentiableWithinAt_arcsin_Ici] using this

theorem differentiableAt_arcsin {x : ℝ} : DifferentiableAt ℝ arcsin x ↔ x ≠ -1 ∧ x ≠ 1 :=
  ⟨fun h => ⟨differentiableWithinAt_arcsin_Ici.1 h.differentiableWithinAt,
      differentiableWithinAt_arcsin_Iic.1 h.differentiableWithinAt⟩,
    fun h => (hasDerivAt_arcsin h.1 h.2).differentiableAt⟩
