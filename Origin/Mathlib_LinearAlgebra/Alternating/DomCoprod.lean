/-
Extracted from LinearAlgebra/Alternating/DomCoprod.lean
Genuine: 4 of 5 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Exterior product of alternating maps

In this file we define `AlternatingMap.domCoprod`
to be the exterior product of two alternating maps,
taking values in the tensor product of the codomains of the original maps.
-/

open TensorProduct

variable {ιa ιb : Type*} [Fintype ιa] [Fintype ιb]

variable {R' : Type*} {Mᵢ N₁ N₂ : Type*} [CommSemiring R'] [AddCommGroup N₁] [Module R' N₁]
  [AddCommGroup N₂] [Module R' N₂] [AddCommMonoid Mᵢ] [Module R' Mᵢ]

namespace Equiv.Perm

abbrev ModSumCongr (α β : Type*) :=
  _ ⧸ (Equiv.Perm.sumCongrHom α β).range

end Equiv.Perm

namespace AlternatingMap

open Equiv

variable [DecidableEq ιa] [DecidableEq ιb]

set_option backward.isDefEq.respectTransparency false in

def domCoprod.summand (a : Mᵢ [⋀^ιa]→ₗ[R'] N₁) (b : Mᵢ [⋀^ιb]→ₗ[R'] N₂)
    (σ : Perm.ModSumCongr ιa ιb) : MultilinearMap R' (fun _ : ιa ⊕ ιb => Mᵢ) (N₁ ⊗[R'] N₂) :=
  Quotient.liftOn' σ
    (fun σ =>
      Equiv.Perm.sign σ •
        (MultilinearMap.domCoprod ↑a ↑b : MultilinearMap R' (fun _ => Mᵢ) (N₁ ⊗ N₂)).domDomCongr σ)
    fun σ₁ σ₂ H => by
    rw [QuotientGroup.leftRel_apply] at H
    obtain ⟨⟨sl, sr⟩, h⟩ := H
    ext v
    simp only [MultilinearMap.domDomCongr_apply, MultilinearMap.domCoprod_apply,
      coe_multilinearMap, MultilinearMap.smul_apply]
    replace h := inv_mul_eq_iff_eq_mul.mp h.symm
    have : Equiv.Perm.sign (σ₁ * Perm.sumCongrHom _ _ (sl, sr))
      = Equiv.Perm.sign σ₁ * (Equiv.Perm.sign sl * Equiv.Perm.sign sr) := by simp
    rw [h, this, mul_smul, mul_smul, smul_left_cancel_iff, ← TensorProduct.tmul_smul,
      TensorProduct.smul_tmul', a.map_congr_perm _ sl, b.map_congr_perm _ sr]
    simp only [Sum.map_inr, Perm.sumCongrHom_apply, Perm.sumCongr_apply, Sum.map_inl,
      Function.comp_def, Perm.coe_mul]

theorem domCoprod.summand_add_swap_smul_eq_zero (a : Mᵢ [⋀^ιa]→ₗ[R'] N₁)
    (b : Mᵢ [⋀^ιb]→ₗ[R'] N₂) (σ : Perm.ModSumCongr ιa ιb) {v : ιa ⊕ ιb → Mᵢ}
    {i j : ιa ⊕ ιb} (hv : v i = v j) (hij : i ≠ j) :
    domCoprod.summand a b σ v + domCoprod.summand a b (swap i j • σ) v = 0 := by
  induction σ using Quotient.inductionOn'
  dsimp only [Quotient.liftOn'_mk'', Quotient.map'_mk'', MulAction.Quotient.smul_mk,
    domCoprod.summand]
  rw [smul_eq_mul, Perm.sign_mul, Perm.sign_swap hij]
  simp only [one_mul, neg_mul, Function.comp_apply, Units.neg_smul, Perm.coe_mul,
    MultilinearMap.smul_apply, MultilinearMap.neg_apply, MultilinearMap.domDomCongr_apply,
    MultilinearMap.domCoprod_apply]
  convert add_neg_cancel (G := N₁ ⊗[R'] N₂) _ using 6 <;>
    · ext k
      rw [Equiv.apply_swap_eq_self hv]

theorem domCoprod.summand_eq_zero_of_smul_invariant (a : Mᵢ [⋀^ιa]→ₗ[R'] N₁)
    (b : Mᵢ [⋀^ιb]→ₗ[R'] N₂) (σ : Perm.ModSumCongr ιa ιb) {v : ιa ⊕ ιb → Mᵢ}
    {i j : ιa ⊕ ιb} (hv : v i = v j) (hij : i ≠ j) :
    swap i j • σ = σ → domCoprod.summand a b σ v = 0 := by
  induction σ using Quotient.inductionOn' with | _ σ
  dsimp only [Quotient.liftOn'_mk'', Quotient.map'_mk'', MultilinearMap.smul_apply,
    MultilinearMap.domDomCongr_apply, MultilinearMap.domCoprod_apply, domCoprod.summand]
  intro hσ
  obtain ⟨⟨sl, sr⟩, hσ⟩ := QuotientGroup.leftRel_apply.mp (Quotient.exact' hσ)
  rcases hi : σ⁻¹ i with i' | i' <;> rcases hj : σ⁻¹ j with j' | j' <;>
    rw [Perm.inv_eq_iff_eq] at hi hj <;> substs hi hj
  -- the term pairs with and cancels another term
  case inl.inr => simpa using Equiv.congr_fun hσ (Sum.inl i')
  case inr.inl => simpa using Equiv.congr_fun hσ (Sum.inr i')
  -- the term does not pair but is zero
  case inl.inl =>
    suffices (a fun i ↦ v (σ (Sum.inl i))) = 0 by simp_all
    exact AlternatingMap.map_eq_zero_of_eq _ _ hv fun hij' => hij (hij' ▸ rfl)
  case inr.inr =>
    suffices (b fun i ↦ v (σ (Sum.inr i))) = 0 by simp_all
    exact b.map_eq_zero_of_eq _ hv fun hij' => hij (hij' ▸ rfl)
