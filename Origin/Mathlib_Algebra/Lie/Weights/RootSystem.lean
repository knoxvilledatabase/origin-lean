/-
Extracted from Algebra/Lie/Weights/RootSystem.lean
Genuine: 11 of 12 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# The root system associated with a Lie algebra

We show that the roots of a finite-dimensional splitting semisimple Lie algebra over a field of
characteristic 0 form a root system. We achieve this by studying root chains.

## Main results

- `LieAlgebra.IsKilling.apply_coroot_eq_cast`:
  If `β - qα ... β ... β + rα` is the `α`-chain through `β`, then
  `β (coroot α) = q - r`. In particular, it is an integer.

- `LieAlgebra.IsKilling.rootSpace_zsmul_add_ne_bot_iff`:
  The `α`-chain through `β` (`β - qα ... β ... β + rα`) are the only roots of the form `β + kα`.

- `LieAlgebra.IsKilling.eq_neg_or_eq_of_eq_smul`:
  `±α` are the only `K`-multiples of a root `α` that are also (non-zero) roots.

- `LieAlgebra.IsKilling.rootSystem`: The root system of a finite-dimensional Lie algebra with
  non-degenerate Killing form over a field of characteristic zero,
  relative to a splitting Cartan subalgebra.

-/

noncomputable section

namespace LieAlgebra.IsKilling

open LieModule Module

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [IsTriangularizable K H L]

variable (α β : Weight K H L)

set_option backward.privateInPublic true in

private lemma chainLength_aux (hα : α.IsNonZero) {x} (hx : x ∈ rootSpace H (chainTop α β)) :
    ∃ n : ℕ, n • x = ⁅coroot α, x⁆ := by
  by_cases hx' : x = 0
  · exact ⟨0, by simp [hx']⟩
  obtain ⟨h, e, f, isSl2, he, hf⟩ := exists_isSl2Triple_of_weight_isNonZero hα
  obtain rfl := isSl2.h_eq_coroot hα he hf
  have : isSl2.HasPrimitiveVectorWith x (chainTop α β (coroot α)) :=
    have := lie_mem_genWeightSpace_of_mem_genWeightSpace he hx
    ⟨hx', by rw [← lie_eq_smul_of_mem_rootSpace hx]; rfl,
      by rwa [genWeightSpace_add_chainTop α β hα] at this⟩
  obtain ⟨μ, hμ⟩ := this.exists_nat
  exact ⟨μ, by rw [← Nat.cast_smul_eq_nsmul K, ← hμ, lie_eq_smul_of_mem_rootSpace hx]⟩

set_option backward.privateInPublic true in

set_option backward.privateInPublic.warn false in

def chainLength (α β : Weight K H L) : ℕ :=
  letI := Classical.propDecidable
  if hα : α.IsZero then 0 else
    (chainLength_aux α β hα (chainTop α β).exists_ne_zero.choose_spec.1).choose

lemma chainLength_of_isZero (hα : α.IsZero) : chainLength α β = 0 := dif_pos hα

lemma chainLength_nsmul {x} (hx : x ∈ rootSpace H (chainTop α β)) :
    chainLength α β • x = ⁅coroot α, x⁆ := by
  by_cases hα : α.IsZero
  · rw [coroot_eq_zero_iff.mpr hα, chainLength_of_isZero _ _ hα, zero_smul, zero_lie]
  let x' := (chainTop α β).exists_ne_zero.choose
  have h : x' ∈ rootSpace H (chainTop α β) ∧ x' ≠ 0 :=
    (chainTop α β).exists_ne_zero.choose_spec
  obtain ⟨k, rfl⟩ : ∃ k : K, k • x' = x := by
    simpa using (finrank_eq_one_iff_of_nonzero' ⟨x', h.1⟩ (by simpa using h.2)).mp
      (finrank_rootSpace_eq_one _ (chainTop_isNonZero α β hα)) ⟨_, hx⟩
  rw [lie_smul, smul_comm, chainLength, dif_neg hα, (chainLength_aux α β hα h.1).choose_spec]

lemma chainLength_smul {x} (hx : x ∈ rootSpace H (chainTop α β)) :
    (chainLength α β : K) • x = ⁅coroot α, x⁆ := by
  rw [Nat.cast_smul_eq_nsmul, chainLength_nsmul _ _ hx]

lemma apply_coroot_eq_cast' :
    β (coroot α) = ↑(chainLength α β - 2 * chainTopCoeff α β : ℤ) := by
  by_cases hα : α.IsZero
  · rw [coroot_eq_zero_iff.mpr hα, chainLength, dif_pos hα, hα.eq, chainTopCoeff_zero, map_zero,
      CharP.cast_eq_zero, mul_zero, sub_self, Int.cast_zero]
  obtain ⟨x, hx, x_ne0⟩ := (chainTop α β).exists_ne_zero
  have := chainLength_smul _ _ hx
  rw [lie_eq_smul_of_mem_rootSpace hx, ← sub_eq_zero, ← sub_smul,
    smul_eq_zero_iff_left x_ne0, sub_eq_zero, coe_chainTop', nsmul_eq_mul, Pi.natCast_def,
    Pi.add_apply, Pi.mul_apply, root_apply_coroot hα] at this
  simp only [Int.cast_sub, Int.cast_natCast, Int.cast_mul, Int.cast_ofNat, eq_sub_iff_add_eq',
    this, mul_comm (2 : K)]

lemma rootSpace_neg_nsmul_add_chainTop_of_le {n : ℕ} (hn : n ≤ chainLength α β) :
    rootSpace H (-(n • α) + chainTop α β) ≠ ⊥ := by
  by_cases hα : α.IsZero
  · simpa only [hα.eq, smul_zero, neg_zero, chainTop_zero, zero_add, ne_eq] using β.2
  obtain ⟨x, hx, x_ne0⟩ := (chainTop α β).exists_ne_zero
  obtain ⟨h, e, f, isSl2, he, hf⟩ := exists_isSl2Triple_of_weight_isNonZero hα
  obtain rfl := isSl2.h_eq_coroot hα he hf
  have prim : isSl2.HasPrimitiveVectorWith x (chainLength α β : K) :=
    have := lie_mem_genWeightSpace_of_mem_genWeightSpace he hx
    ⟨x_ne0, (chainLength_smul _ _ hx).symm, by rwa [genWeightSpace_add_chainTop _ _ hα] at this⟩
  simp only [← smul_neg, ne_eq, LieSubmodule.eq_bot_iff, not_forall]
  exact ⟨_, toEnd_pow_apply_mem hf hx n, prim.pow_toEnd_f_ne_zero_of_eq_nat rfl hn⟩

lemma chainTopCoeff_le_chainLength : chainTopCoeff α β ≤ chainLength α β := by
  by_cases hα : α.IsZero
  · simp only [hα.eq, chainTopCoeff_zero, zero_le]
  rw [← not_lt, ← Nat.succ_le_iff]
  intro e
  apply genWeightSpace_nsmul_add_ne_bot_of_le α β
    (Nat.sub_le (chainTopCoeff α β) (chainLength α β).succ)
  rw [← Nat.cast_smul_eq_nsmul ℤ, Nat.cast_sub e, sub_smul, sub_eq_neg_add,
    add_assoc, ← coe_chainTop, Nat.cast_smul_eq_nsmul]
  exact rootSpace_neg_nsmul_add_chainTop_of_lt α β hα (Nat.lt_succ_self _)

lemma chainBotCoeff_add_chainTopCoeff :
    chainBotCoeff α β + chainTopCoeff α β = chainLength α β := by
  by_cases hα : α.IsZero
  · rw [hα.eq, chainTopCoeff_zero, chainBotCoeff_zero, zero_add, chainLength_of_isZero α β hα]
  apply le_antisymm
  · rw [← Nat.le_sub_iff_add_le (chainTopCoeff_le_chainLength α β),
      ← not_lt, ← Nat.succ_le_iff, chainBotCoeff, ← Weight.coe_neg]
    intro e
    apply genWeightSpace_nsmul_add_ne_bot_of_le _ _ e
    rw [← Nat.cast_smul_eq_nsmul ℤ, Nat.cast_succ, Nat.cast_sub (chainTopCoeff_le_chainLength α β),
      LieModule.Weight.coe_neg, smul_neg, ← neg_smul, neg_add_rev, neg_sub, sub_eq_neg_add,
      ← add_assoc, ← neg_add_rev, add_smul, add_assoc, ← coe_chainTop, neg_smul,
      ← @Nat.cast_one ℤ, ← Nat.cast_add, Nat.cast_smul_eq_nsmul]
    exact rootSpace_neg_nsmul_add_chainTop_of_lt α β hα (Nat.lt_succ_self _)
  · rw [← not_lt]
    intro e
    apply rootSpace_neg_nsmul_add_chainTop_of_le α β e
    rw [← Nat.succ_add, ← Nat.cast_smul_eq_nsmul ℤ, ← neg_smul, coe_chainTop, ← add_assoc,
      ← add_smul, Nat.cast_add, neg_add, add_assoc, neg_add_cancel, add_zero, neg_smul, ← smul_neg,
      Nat.cast_smul_eq_nsmul]
    exact genWeightSpace_chainTopCoeff_add_one_nsmul_add (-α) β (Weight.IsNonZero.neg hα)

lemma chainTopCoeff_add_chainBotCoeff :
    chainTopCoeff α β + chainBotCoeff α β = chainLength α β := by
  rw [add_comm, chainBotCoeff_add_chainTopCoeff]

lemma chainBotCoeff_le_chainLength : chainBotCoeff α β ≤ chainLength α β :=
  (Nat.le_add_left _ _).trans_eq (chainTopCoeff_add_chainBotCoeff α β)
