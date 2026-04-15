/-
Extracted from NumberTheory/ModularForms/EisensteinSeries/E2/MDifferentiable.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# MDifferentiability of the weight 2 Eisenstein series

We show that the weight 2 Eisenstein series `E2` is MDifferentiable (i.e. holomorphic as a
function `ℍ → ℂ`). The proof uses the relation between `E2` and the logarithmic derivative of
the Dedekind eta function.
-/

open UpperHalfPlane hiding I

open Real Complex EisensteinSeries ModularForm Manifold

lemma E2_mdifferentiable : MDiff E2 := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  have hη : DifferentiableOn ℂ η _ := fun z hz ↦
    (differentiableAt_eta_of_mem_upperHalfPlaneSet hz).differentiableWithinAt
  have hlog : DifferentiableOn ℂ (logDeriv η) _ :=
    (hη.deriv isOpen_upperHalfPlaneSet).div hη (fun _ hz ↦ eta_ne_zero hz)
  refine (hlog.const_mul (π * I / 12)⁻¹).congr (fun z hz ↦ ?_)
  simp [ofComplex_apply_of_im_pos hz, logDeriv_eta_eq_E2 ⟨z, hz⟩]
  field_simp

end
