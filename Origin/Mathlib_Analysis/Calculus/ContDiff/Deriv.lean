/-
Extracted from Analysis/Calculus/ContDiff/Deriv.lean
Genuine: 9 of 9 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Higher differentiability in one dimension

The general theory of higher derivatives in Mathlib is developed using the Fréchet derivative
`fderiv`; but for maps defined on the field, the one-dimensional derivative `deriv` is often easier
to use. In this file, we reformulate some higher smoothness results in terms of `deriv`.

## Tags

derivative, differentiability, higher derivative, `C^n`, multilinear, Taylor series, formal series
-/

public noncomputable section

open scoped ContDiff

open Set

variable {𝕜 F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {m n : WithTop ℕ∞} {f : 𝕜 → F} {s : Set 𝕜}

theorem contDiffOn_succ_iff_derivWithin (hs : UniqueDiffOn 𝕜 s) :
    ContDiffOn 𝕜 (n + 1) f s ↔
      DifferentiableOn 𝕜 f s ∧ (n = ω → AnalyticOn 𝕜 f s) ∧ ContDiffOn 𝕜 n (derivWithin f s) s := by
  have : derivWithin f s =
      ContinuousLinearMap.toSpanSingletonCLE.symm ∘ fderivWithin 𝕜 f s := by
    ext; simp [← fderivWithin_derivWithin]
  simp [contDiffOn_succ_iff_fderivWithin hs, this, ContinuousLinearEquiv.comp_contDiffOn_iff]

theorem contDiffOn_one_iff_derivWithin (hs : UniqueDiffOn 𝕜 s) :
    ContDiffOn 𝕜 1 f s ↔ DifferentiableOn 𝕜 f s ∧ ContinuousOn (derivWithin f s) s := by
  rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl, contDiffOn_succ_iff_derivWithin hs]
  simp

theorem contDiffOn_infty_iff_derivWithin (hs : UniqueDiffOn 𝕜 s) :
    ContDiffOn 𝕜 ∞ f s ↔ DifferentiableOn 𝕜 f s ∧ ContDiffOn 𝕜 ∞ (derivWithin f s) s := by
  rw [show ∞ = ∞ + 1 by rfl, contDiffOn_succ_iff_derivWithin hs]
  simp

theorem contDiffOn_succ_iff_deriv_of_isOpen (hs : IsOpen s) :
    ContDiffOn 𝕜 (n + 1) f s ↔
      DifferentiableOn 𝕜 f s ∧ (n = ω → AnalyticOn 𝕜 f s) ∧ ContDiffOn 𝕜 n (deriv f) s := by
  rw [contDiffOn_succ_iff_derivWithin hs.uniqueDiffOn]
  exact Iff.rfl.and (Iff.rfl.and (contDiffOn_congr fun _ => derivWithin_of_isOpen hs))

theorem contDiffOn_infty_iff_deriv_of_isOpen (hs : IsOpen s) :
    ContDiffOn 𝕜 ∞ f s ↔ DifferentiableOn 𝕜 f s ∧ ContDiffOn 𝕜 ∞ (deriv f) s := by
  rw [show ∞ = ∞ + 1 by rfl, contDiffOn_succ_iff_deriv_of_isOpen hs]
  simp

protected theorem ContDiffOn.derivWithin (hf : ContDiffOn 𝕜 n f s) (hs : UniqueDiffOn 𝕜 s)
    (hmn : m + 1 ≤ n) : ContDiffOn 𝕜 m (derivWithin f s) s :=
  ((contDiffOn_succ_iff_derivWithin hs).1 (hf.of_le hmn)).2.2

theorem ContDiffOn.deriv_of_isOpen (hf : ContDiffOn 𝕜 n f s) (hs : IsOpen s) (hmn : m + 1 ≤ n) :
    ContDiffOn 𝕜 m (deriv f) s :=
  (hf.derivWithin hs.uniqueDiffOn hmn).congr fun _ hx => (derivWithin_of_isOpen hs hx).symm

theorem ContDiffOn.continuousOn_derivWithin (h : ContDiffOn 𝕜 n f s) (hs : UniqueDiffOn 𝕜 s)
    (hn : 1 ≤ n) : ContinuousOn (derivWithin f s) s := by
  rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl] at hn
  exact ((contDiffOn_succ_iff_derivWithin hs).1 (h.of_le hn)).2.2.continuousOn

theorem ContDiffOn.continuousOn_deriv_of_isOpen (h : ContDiffOn 𝕜 n f s) (hs : IsOpen s)
    (hn : 1 ≤ n) : ContinuousOn (deriv f) s := by
  rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl] at hn
  exact ((contDiffOn_succ_iff_deriv_of_isOpen hs).1 (h.of_le hn)).2.2.continuousOn
