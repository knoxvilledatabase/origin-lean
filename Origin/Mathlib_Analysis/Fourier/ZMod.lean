/-
Extracted from Analysis/Fourier/ZMod.lean
Genuine: 5 of 5 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Fourier theory on `ZMod N`

Basic definitions and properties of the discrete Fourier transform for functions on `ZMod N`
(taking values in an arbitrary `ℂ`-vector space).

### Main definitions and results

* `ZMod.dft`: the Fourier transform, with respect to the standard additive character
  `ZMod.stdAddChar` (mapping `j mod N` to `exp (2 * π * I * j / N)`). The notation `𝓕`, scoped in
  namespace `ZMod`, is available for this.
* `ZMod.dft_dft`: the Fourier inversion formula.
* `DirichletCharacter.fourierTransform_eq_inv_mul_gaussSum`: the discrete Fourier transform of a
  primitive Dirichlet character `χ` is a Gauss sum times `χ⁻¹`.
-/

open MeasureTheory Finset AddChar ZMod

namespace ZMod

variable {N : ℕ} [NeZero N] {E : Type*} [AddCommGroup E] [Module ℂ E]

section private_defs

set_option backward.privateInPublic true in

private noncomputable def auxDFT (Φ : ZMod N → E) (k : ZMod N) : E :=
  ∑ j : ZMod N, stdAddChar (-(j * k)) • Φ j

private lemma auxDFT_neg (Φ : ZMod N → E) : auxDFT (fun j ↦ Φ (-j)) = fun k ↦ auxDFT Φ (-k) := by
  ext1 k; simpa only [auxDFT] using
    Fintype.sum_equiv (Equiv.neg _) _ _ (fun j ↦ by rw [Equiv.neg_apply, neg_mul_neg])

private lemma auxDFT_auxDFT (Φ : ZMod N → E) : auxDFT (auxDFT Φ) = fun j ↦ (N : ℂ) • Φ (-j) := by
  ext1 j
  simp only [auxDFT, mul_comm _ j, smul_sum, ← smul_assoc, smul_eq_mul, ← map_add_eq_mul, ←
    neg_add, ← add_mul]
  rw [sum_comm]
  simp only [← sum_smul, ← neg_mul]
  have h1 (t : ZMod N) : ∑ i, stdAddChar (t * i) = if t = 0 then ↑N else 0 := by
    split_ifs with h
    · simp only [h, zero_mul, map_zero_eq_one, sum_const, card_univ, card,
        nsmul_eq_mul, mul_one]
    · exact sum_eq_zero_of_ne_one (isPrimitive_stdAddChar N h)
  have h2 (x j : ZMod N) : -(j + x) = 0 ↔ x = -j := by
    rw [neg_add, add_comm, add_eq_zero_iff_neg_eq, neg_neg]
  simp only [h1, h2, ite_smul, zero_smul, sum_ite_eq', mem_univ, ite_true]

private lemma auxDFT_smul (c : ℂ) (Φ : ZMod N → E) :
    auxDFT (c • Φ) = c • auxDFT Φ := by
  ext; simp only [Pi.smul_def, auxDFT, smul_sum, smul_comm c]

end private_defs

section defs

set_option backward.privateInPublic true in

set_option backward.privateInPublic.warn false in

noncomputable def dft : (ZMod N → E) ≃ₗ[ℂ] (ZMod N → E) where
  toFun := auxDFT
  map_add' Φ₁ Φ₂ := by
    ext; simp only [auxDFT, Pi.add_def, smul_add, sum_add_distrib]
  map_smul' c Φ := by
    ext; simp only [auxDFT, Pi.smul_apply, RingHom.id_apply, smul_sum, smul_comm c]
  invFun Φ k := (N : ℂ)⁻¹ • auxDFT Φ (-k)
  left_inv Φ := by
    simp only [auxDFT_auxDFT, neg_neg, ← mul_smul, inv_mul_cancel₀ (NeZero.ne _), one_smul]
  right_inv Φ := by
    ext1 j
    simp only [← Pi.smul_def, auxDFT_smul, auxDFT_neg, auxDFT_auxDFT, neg_neg, ← mul_smul,
      inv_mul_cancel₀ (NeZero.ne _), one_smul]
