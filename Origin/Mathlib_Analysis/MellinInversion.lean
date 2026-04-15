/-
Extracted from Analysis/MellinInversion.lean
Genuine: 5 of 5 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Mellin inversion formula

We derive the Mellin inversion formula as a consequence of the Fourier inversion formula.

## Main results
- `mellin_inversion`: The inverse Mellin transform of the Mellin transform applied to `x > 0` is x.
-/

open Real Complex Set MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

open scoped FourierTransform

private theorem rexp_neg_deriv_aux :
    ∀ x ∈ univ, HasDerivWithinAt (rexp ∘ Neg.neg) (-rexp (-x)) univ x :=
  fun x _ ↦ mul_neg_one (rexp (-x)) ▸
    ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).hasDerivWithinAt

private theorem rexp_neg_image_aux : rexp ∘ Neg.neg '' univ = Ioi 0 := by
  rw [Set.image_comp, Set.image_univ_of_surjective neg_surjective, Set.image_univ, Real.range_exp]

private theorem rexp_neg_injOn_aux : univ.InjOn (rexp ∘ Neg.neg) :=
  Real.exp_injective.injOn.comp neg_injective.injOn (univ.mapsTo_univ _)

private theorem rexp_cexp_aux (x : ℝ) (s : ℂ) (f : E) :
    rexp (-x) • cexp (-↑x) ^ (s - 1) • f = cexp (-s * ↑x) • f := by
  change (rexp (-x) : ℂ) • _ = _ • f
  rw [← smul_assoc, smul_eq_mul]
  push_cast
  conv in cexp _ * _ => lhs; rw [← cpow_one (cexp _)]
  rw [← cpow_add _ _ (Complex.exp_ne_zero _), cpow_def_of_ne_zero (Complex.exp_ne_zero _),
    Complex.log_exp (by simp [pi_pos]) (by simpa using pi_nonneg)]
  ring_nf

set_option backward.isDefEq.respectTransparency false in

theorem mellin_eq_fourier (f : ℝ → E) {s : ℂ} :
    mellin f s = 𝓕 (fun (u : ℝ) ↦ (Real.exp (-s.re * u) • f (Real.exp (-u)))) (s.im / (2 * π)) :=
  calc
    mellin f s
      = ∫ (u : ℝ), Complex.exp (-s * u) • f (Real.exp (-u)) := by
      rw [mellin, ← rexp_neg_image_aux, integral_image_eq_integral_abs_deriv_smul
        MeasurableSet.univ rexp_neg_deriv_aux rexp_neg_injOn_aux]
      simp [rexp_cexp_aux]
    _ = ∫ (u : ℝ), Complex.exp (↑(-2 * π * (u * (s.im / (2 * π)))) * I) •
        (Real.exp (-s.re * u) • f (Real.exp (-u))) := by
      congr
      ext u
      trans Complex.exp (-s.im * u * I) • (Real.exp (-s.re * u) • f (Real.exp (-u)))
      · conv => lhs; rw [← re_add_im s]
        rw [neg_add, add_mul, Complex.exp_add, mul_comm, ← smul_eq_mul, smul_assoc]
        norm_cast
        push_cast
        ring_nf
      congr
      simp [field]
    _ = 𝓕 (fun (u : ℝ) ↦ (Real.exp (-s.re * u) • f (Real.exp (-u)))) (s.im / (2 * π)) := by
      simp [fourier_eq', mul_comm (_ / _)]
