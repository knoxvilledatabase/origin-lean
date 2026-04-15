/-
Extracted from LinearAlgebra/RootSystem/Finite/Lemmas.lean
Genuine: 17 of 21 | Dissolved: 2 | Infrastructure: 2
-/
import Origin.Core

/-!
# Structural lemmas about finite crystallographic root pairings

In this file we gather basic lemmas necessary for the classification of finite crystallographic
root pairings.

## Main results:

* `RootPairing.coxeterWeightIn_mem_set_of_isCrystallographic`: the Coxeter weights of a finite
  crystallographic root pairing belong to the set `{0, 1, 2, 3, 4}`.
* `RootPairing.root_sub_root_mem_of_pairingIn_pos`: if `α ≠ β` are both roots of a finite
  crystallographic root pairing, and the pairing of `α` with `β` is positive, then `α - β` is also
  a root.
* `RootPairing.root_add_root_mem_of_pairingIn_neg`: if `α ≠ -β` are both roots of a finite
  crystallographic root pairing, and the pairing of `α` with `β` is negative, then `α + β` is also
  a root.

-/

noncomputable section

open Function Set

open Submodule (span)

open FaithfulSMul (algebraMap_injective)

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

namespace RootPairing

variable (P : RootPairing ι R M N) [Finite ι]

local notation "Φ" => range P.root

local notation "α" => P.root

lemma coxeterWeightIn_le_four (S : Type*)
    [CommRing S] [LinearOrder S] [IsStrictOrderedRing S] [Algebra S R] [FaithfulSMul S R]
    [Module S M] [IsScalarTower S R M] [P.IsValuedIn S] (i j : ι) :
    P.coxeterWeightIn S i j ≤ 4 := by
  have : Fintype ι := Fintype.ofFinite ι
  let ri : span S Φ := ⟨α i, Submodule.subset_span (mem_range_self _)⟩
  let rj : span S Φ := ⟨α j, Submodule.subset_span (mem_range_self _)⟩
  set li := (P.posRootForm S).rootLength i
  set lj := (P.posRootForm S).rootLength j
  set lij := (P.posRootForm S).posForm ri rj
  obtain ⟨si, hsi, hsi'⟩ := (P.posRootForm S).exists_pos_eq i
  obtain ⟨sj, hsj, hsj'⟩ := (P.posRootForm S).exists_pos_eq j
  replace hsi' : si = li := algebraMap_injective S R <| by simpa [li] using hsi'
  replace hsj' : sj = lj := algebraMap_injective S R <| by simpa [lj] using hsj'
  rw [hsi'] at hsi
  rw [hsj'] at hsj
  have cs : 4 * lij ^ 2 ≤ 4 * (li * lj) := by
    rw [mul_le_mul_iff_right₀ four_pos]
    exact (P.posRootForm S).posForm.apply_sq_le_of_symm (zero_le_posForm _ _ ·)
      (P.posRootForm S).isSymm_posForm ri rj
  have key : 4 • lij ^ 2 = P.coxeterWeightIn S i j • (li * lj) := by
    apply algebraMap_injective S R
    simpa [map_ofNat, lij, posRootForm, ri, rj, li, lj] using
       P.four_smul_rootForm_sq_eq_coxeterWeight_smul i j
  simp only [nsmul_eq_mul, smul_eq_mul, Nat.cast_ofNat] at key
  rwa [key, mul_le_mul_iff_left₀ (by positivity)] at cs

variable [CharZero R] [P.IsCrystallographic] (i j : ι)

lemma coxeterWeightIn_mem_set_of_isCrystallographic :
    P.coxeterWeightIn ℤ i j ∈ ({0, 1, 2, 3, 4} : Set ℤ) := by
  have : Fintype ι := Fintype.ofFinite ι
  obtain ⟨n, hcn⟩ : ∃ n : ℕ, P.coxeterWeightIn ℤ i j = n := by
    have : 0 ≤ P.coxeterWeightIn ℤ i j := by
      simpa only [P.algebraMap_coxeterWeightIn] using P.coxeterWeight_nonneg (P.posRootForm ℤ) i j
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le this
    exact ⟨n, by simp [hn]⟩
  have : P.coxeterWeightIn ℤ i j ≤ 4 := P.coxeterWeightIn_le_four ℤ i j
  simp only [hcn, mem_insert_iff, mem_singleton_iff] at this ⊢
  norm_cast at this ⊢
  lia

variable [IsDomain R]

open scoped IsDomain

lemma pairingIn_pairingIn_mem_set_of_isCrystallographic :
    (P.pairingIn ℤ i j, P.pairingIn ℤ j i) ∈
      ({(0, 0), (1, 1), (-1, -1), (1, 2), (2, 1), (-1, -2), (-2, -1), (1, 3), (3, 1), (-1, -3),
        (-3, -1), (4, 1), (1, 4), (-4, -1), (-1, -4), (2, 2), (-2, -2)} : Set (ℤ × ℤ)) := by
  refine (Int.mul_mem_zero_one_two_three_four_iff ?_).mp
    (P.coxeterWeightIn_mem_set_of_isCrystallographic i j)
  simpa [← P.algebraMap_pairingIn ℤ] using P.pairing_eq_zero_iff' (i := i) (j := j)

lemma pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed [P.IsReduced] :
    (P.pairingIn ℤ i j, P.pairingIn ℤ j i) ∈
      ({(0, 0), (1, 1), (-1, -1), (1, 2), (2, 1), (-1, -2), (-2, -1), (1, 3), (3, 1), (-1, -3),
        (-3, -1), (2, 2), (-2, -2)} : Set (ℤ × ℤ)) := by
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  rcases eq_or_ne i j with rfl | h₁; · simp
  rcases eq_or_ne (α i) (-α j) with h₂ | h₂; · simp_all
  have aux₁ := P.pairingIn_pairingIn_mem_set_of_isCrystallographic i j
  have aux₂ : P.pairingIn ℤ i j * P.pairingIn ℤ j i ≠ 4 := P.coxeterWeightIn_ne_four ℤ h₁ h₂
  aesop -- https://github.com/leanprover-community/mathlib4/issues/24551 (this should be faster)

lemma pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed' [P.IsReduced]
    (hij : α i ≠ α j) (hij' : α i ≠ -α j) :
    (P.pairingIn ℤ i j, P.pairingIn ℤ j i) ∈
      ({(0, 0), (1, 1), (-1, -1), (1, 2), (2, 1), (-1, -2), (-2, -1), (1, 3), (3, 1), (-1, -3),
        (-3, -1)} : Set (ℤ × ℤ)) := by
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  have := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed i j
  simp_all

variable {P} in

lemma RootPositiveForm.rootLength_le_of_pairingIn_eq (B : P.RootPositiveForm ℤ) {i j : ι}
    (hij : P.pairingIn ℤ i j = -1 ∨ P.pairingIn ℤ i j = 1) :
    B.rootLength i ≤ B.rootLength j := by
  have h : (P.pairingIn ℤ i j, P.pairingIn ℤ j i) ∈
      ({(1, 1), (1, 2), (1, 3), (1, 4), (-1, -1), (-1, -2), (-1, -3), (-1, -4)} : Set (ℤ × ℤ)) := by
    have := P.pairingIn_pairingIn_mem_set_of_isCrystallographic i j
    aesop -- https://github.com/leanprover-community/mathlib4/issues/24551 (this should be faster)
  simp only [mem_insert_iff, mem_singleton_iff, Prod.mk_one_one, Prod.mk_eq_one, Prod.mk.injEq] at h
  have h' := B.pairingIn_mul_eq_pairingIn_mul_swap i j
  have hi := B.rootLength_pos i
  rcases h with hij' | hij' | hij' | hij' | hij' | hij' | hij' | hij' <;>
  rw [hij'.1, hij'.2] at h' <;> lia

variable {P} in

lemma RootPositiveForm.rootLength_lt_of_pairingIn_notMem
    (B : P.RootPositiveForm ℤ) {i j : ι}
    (hne : α i ≠ α j) (hne' : α i ≠ -α j)
    (hij : P.pairingIn ℤ i j ∉ ({-1, 0, 1} : Set ℤ)) :
    B.rootLength j < B.rootLength i := by
  have hij' : P.pairingIn ℤ i j = -3 ∨ P.pairingIn ℤ i j = -2 ∨ P.pairingIn ℤ i j = 2 ∨
      P.pairingIn ℤ i j = 3 ∨ P.pairingIn ℤ i j = -4 ∨ P.pairingIn ℤ i j = 4 := by
    have := P.pairingIn_pairingIn_mem_set_of_isCrystallographic i j
    aesop -- https://github.com/leanprover-community/mathlib4/issues/24551 (this should be faster)
  have aux₁ : P.pairingIn ℤ j i = -1 ∨ P.pairingIn ℤ j i = 1 := by
    have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
    have := P.pairingIn_pairingIn_mem_set_of_isCrystallographic i j
    aesop -- https://github.com/leanprover-community/mathlib4/issues/24551 (this should be faster)
  have aux₂ := B.pairingIn_mul_eq_pairingIn_mul_swap i j
  have hi := B.rootLength_pos i
  rcases aux₁ with hji | hji <;> rcases hij' with hij' | hij' | hij' | hij' | hij' | hij' <;>
  rw [hji, hij'] at aux₂ <;> lia

variable {i j} in

lemma pairingIn_pairingIn_mem_set_of_length_eq {B : P.InvariantForm}
    (len_eq : B.form (α i) (α i) = B.form (α j) (α j)) :
    (P.pairingIn ℤ i j, P.pairingIn ℤ j i) ∈
      ({(0, 0), (1, 1), (-1, -1), (2, 2), (-2, -2)} : Set (ℤ × ℤ)) := by
  replace len_eq : P.pairingIn ℤ i j = P.pairingIn ℤ j i := by
    simp only [← (FaithfulSMul.algebraMap_injective ℤ R).eq_iff, algebraMap_pairingIn]
    exact mul_right_cancel₀ (B.ne_zero j) (len_eq ▸ B.pairing_mul_eq_pairing_mul_swap j i)
  have := P.pairingIn_pairingIn_mem_set_of_isCrystallographic i j
  aesop -- https://github.com/leanprover-community/mathlib4/issues/24551 (this should be faster)

variable {i j} in

lemma pairingIn_pairingIn_mem_set_of_length_eq_of_ne {B : P.InvariantForm}
    (len_eq : B.form (α i) (α i) = B.form (α j) (α j))
    (ne : i ≠ j) (ne' : α i ≠ -α j) :
    (P.pairingIn ℤ i j, P.pairingIn ℤ j i) ∈ ({(0, 0), (1, 1), (-1, -1)} : Set (ℤ × ℤ)) := by
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  have := P.pairingIn_pairingIn_mem_set_of_length_eq len_eq
  simp_all

omit [Finite ι] in

lemma coxeterWeightIn_eq_zero_iff :
    P.coxeterWeightIn ℤ i j = 0 ↔ P.pairingIn ℤ i j = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [coxeterWeightIn, h, zero_mul]⟩
  rwa [← (algebraMap_injective ℤ R).eq_iff, map_zero, algebraMap_coxeterWeightIn,
    RootPairing.coxeterWeight_zero_iff_isOrthogonal, IsOrthogonal,
    P.pairing_eq_zero_iff' (i := j) (j := i), and_self, ← P.algebraMap_pairingIn ℤ,
    FaithfulSMul.algebraMap_eq_zero_iff] at h

variable {i j}

lemma root_sub_root_mem_of_pairingIn_pos (h : 0 < P.pairingIn ℤ i j) (h' : i ≠ j) :
    α i - α j ∈ Φ := by
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  have : Module.IsReflexive R N := .of_isPerfPair P.flip.toLinearMap
  have : IsAddTorsionFree M := .of_isTorsionFree R M
  by_cases hli : LinearIndependent R ![α i, α j]
  · -- The case where the two roots are linearly independent
    suffices P.pairingIn ℤ i j = 1 ∨ P.pairingIn ℤ j i = 1 by
      rcases this with h₁ | h₁
      · replace h₁ : P.pairing i j = 1 := by simpa [← P.algebraMap_pairingIn ℤ]
        exact ⟨P.reflectionPerm j i, by simpa [h₁] using P.reflection_apply_root j i⟩
      · replace h₁ : P.pairing j i = 1 := by simpa [← P.algebraMap_pairingIn ℤ]
        rw [← neg_mem_range_root_iff, neg_sub]
        exact ⟨P.reflectionPerm i j, by simpa [h₁] using P.reflection_apply_root i j⟩
    have : P.coxeterWeightIn ℤ i j ∈ ({1, 2, 3} : Set _) := by
      have aux₁ := P.coxeterWeightIn_mem_set_of_isCrystallographic i j
      have aux₂ := (linearIndependent_iff_coxeterWeightIn_ne_four P ℤ).mp hli
      have aux₃ : P.coxeterWeightIn ℤ i j ≠ 0 := by
        simpa only [ne_eq, P.coxeterWeightIn_eq_zero_iff] using h.ne'
      simp_all
    simp_rw [coxeterWeightIn, Int.mul_mem_one_two_three_iff, mem_insert_iff, mem_singleton_iff,
      Prod.mk.injEq] at this
    lia
  · -- The case where the two roots are linearly dependent
    have : (P.pairingIn ℤ i j, P.pairingIn ℤ j i) ∈ ({(1, 4), (2, 2), (4, 1)} : Set _) := by
      have := P.pairingIn_pairingIn_mem_set_of_isCrystallographic i j
      replace hli : P.pairingIn ℤ i j * P.pairingIn ℤ j i = 4 :=
        (P.coxeterWeightIn_eq_four_iff_not_linearIndependent ℤ).mpr hli
      aesop -- https://github.com/leanprover-community/mathlib4/issues/24551 (this should be faster)
    simp only [mem_insert_iff, mem_singleton_iff, Prod.mk.injEq] at this
    rcases this with hij | hij | hij
    · rw [(P.pairingIn_one_four_iff ℤ i j).mp hij, two_smul, sub_add_cancel_right]
      exact neg_root_mem P i
    · rw [P.pairingIn_two_two_iff] at hij
      contradiction
    · rw [and_comm] at hij
      simp [(P.pairingIn_one_four_iff ℤ j i).mp hij, two_smul]

lemma root_add_root_mem_of_pairingIn_neg (h : P.pairingIn ℤ i j < 0) (h' : α i ≠ -α j) :
    α i + α j ∈ Φ := by
  let _i := P.indexNeg
  replace h : 0 < P.pairingIn ℤ i (-j) := by simpa
  replace h' : i ≠ -j := by contrapose h'; simp [h']
  simpa using P.root_sub_root_mem_of_pairingIn_pos h h'

lemma pairingIn_eq_zero_of_add_notMem_of_sub_notMem (hp : i ≠ j) (hn : α i ≠ -α j)
    (h_add : α i + α j ∉ Φ) (h_sub : α i - α j ∉ Φ) :
    P.pairingIn ℤ i j = 0 := by
  apply le_antisymm
  · contrapose! h_sub
    exact root_sub_root_mem_of_pairingIn_pos P h_sub hp
  · contrapose! h_add
    exact root_add_root_mem_of_pairingIn_neg P h_add hn

lemma pairing_eq_zero_of_add_notMem_of_sub_notMem (hp : i ≠ j) (hn : α i ≠ -α j)
    (h_add : α i + α j ∉ Φ) (h_sub : α i - α j ∉ Φ) :
    P.pairing i j = 0 := by
  rw [← P.algebraMap_pairingIn ℤ, P.pairingIn_eq_zero_of_add_notMem_of_sub_notMem hp hn h_add h_sub,
    map_zero]

omit [Finite ι] in

-- DISSOLVED: root_mem_submodule_iff_of_add_mem_invtSubmodule

namespace InvariantForm

variable [P.IsReduced] (B : P.InvariantForm)

variable {P}

-- DISSOLVED: apply_eq_or_aux

variable [P.IsIrreducible]

lemma apply_eq_or (i j : ι) :
    B.form (α i) (α i) = B.form (α j) (α j) ∨
    B.form (α i) (α i) = 2 * B.form (α j) (α j) ∨
    B.form (α i) (α i) = 3 * B.form (α j) (α j) ∨
    B.form (α j) (α j) = 2 * B.form (α i) (α i) ∨
    B.form (α j) (α j) = 3 * B.form (α i) (α i) := by
  obtain ⟨j', h₁, h₂⟩ := P.exists_form_eq_form_and_form_ne_zero B i j
  suffices P.pairingIn ℤ i j' ≠ 0 by simp only [← h₁, B.apply_eq_or_aux i j' this]
  contrapose h₂
  replace h₂ : P.pairing i j' = 0 := by rw [← P.algebraMap_pairingIn ℤ, h₂, map_zero]
  exact (B.apply_root_root_zero_iff i j').mpr h₂

lemma apply_eq_or_of_apply_ne
    (h : B.form (α i) (α i) ≠ B.form (α j) (α j)) (k : ι) :
    B.form (α k) (α k) = B.form (α i) (α i) ∨
    B.form (α k) (α k) = B.form (α j) (α j) := by
  have : Nonempty ι := ⟨i⟩
  obtain ⟨i', j', h'⟩ := B.exists_apply_eq_or
  rcases h' i with hi | hi <;>
  rcases h' j with hj | hj <;>
  specialize h' k <;>
  aesop

end InvariantForm

lemma forall_pairingIn_eq_swap_or [P.IsReduced] [P.IsIrreducible] :
    (∀ i j, P.pairingIn ℤ i j = P.pairingIn ℤ j i ∨
            P.pairingIn ℤ i j = 2 * P.pairingIn ℤ j i ∨
            P.pairingIn ℤ j i = 2 * P.pairingIn ℤ i j) ∨
    (∀ i j, P.pairingIn ℤ i j = P.pairingIn ℤ j i ∨
            P.pairingIn ℤ i j = 3 * P.pairingIn ℤ j i ∨
            P.pairingIn ℤ j i = 3 * P.pairingIn ℤ i j) := by
  simpa only [← P.algebraMap_pairingIn ℤ, eq_intCast, ← Int.cast_mul, Int.cast_inj,
    ← map_ofNat (algebraMap ℤ R)] using P.forall_pairing_eq_swap_or

end RootPairing
