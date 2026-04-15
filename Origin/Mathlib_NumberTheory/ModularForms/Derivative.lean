/-
Extracted from NumberTheory/ModularForms/Derivative.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Derivatives of modular forms

This file defines normalized derivative $D = \frac{1}{2\pi i} \frac{d}{dz}$
and serre dervative $\partial_k := D - \frac{k}{12} E_2$ of modular forms.

TODO:
- Serre derivative preserves modularity, i.e. $\partial_k (M_k) \subseteq M_{k+2}$.
- Use above, prove Ramanujan's identities. See [here](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/main/SpherePacking/ModularForms/RamanujanIdentities.lean)
  for `sorry`-free proofs.
-/

open UpperHalfPlane hiding I

open Real Complex

open scoped Manifold

namespace Derivative

def normalizedDerivOfComplex (F : ℍ → ℂ) (z : ℍ) : ℂ := (2 * π * I)⁻¹ * deriv (F ∘ ofComplex) z

scoped notation "D" => normalizedDerivOfComplex

theorem normalizedDerivOfComplex_mdifferentiable {F : ℍ → ℂ} (hF : MDiff F) : MDiff (D F) := by
  rw [UpperHalfPlane.mdifferentiable_iff] at hF ⊢
  let c : ℂ := (2 * π * I)⁻¹
  have hDeriv : DifferentiableOn ℂ (fun z ↦ c * deriv (F ∘ ofComplex) z) upperHalfPlaneSet := by
    simpa [c] using (hF.deriv isOpen_upperHalfPlaneSet).const_mul ((2 * π * I)⁻¹)
  refine hDeriv.congr ?_
  intro z hz
  simp [normalizedDerivOfComplex, c, Function.comp_apply, ofComplex_apply_of_im_pos hz]

/-!
Basic properties of normalized derivative.
-/
