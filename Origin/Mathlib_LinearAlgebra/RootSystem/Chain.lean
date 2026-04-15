/-
Extracted from LinearAlgebra/RootSystem/Chain.lean
Genuine: 21 of 21 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Chains of roots

Given roots `α` and `β`, the `α`-chain through `β` is the set of roots of the form `α + z • β`
for an integer `z`. This is known as a "root chain" and also a "root string". For linearly
independent roots in finite crystallographic root pairings, these chains are always unbroken, i.e.,
of the form: `β - q • α, ..., β - α, β, β + α, ..., β + p • α` for natural numbers `p`, `q`, and the
length, `p + q` is at most 3.

## Main definitions / results:
* `RootPairing.chainTopCoeff`: the natural number `p` in the chain
  `β - q • α, ..., β - α, β, β + α, ..., β + p • α`
* `RootPairing.chainTopCoeff`: the natural number `q` in the chain
  `β - q • α, ..., β - α, β, β + α, ..., β + p • α`
* `RootPairing.root_add_zsmul_mem_range_iff`: every chain is an interval (aka unbroken).
* `RootPairing.chainBotCoeff_add_chainTopCoeff_le`: every chain has length at most three.

-/

noncomputable section

open FaithfulSMul Function Set Submodule

variable {ι R M N : Type*} [Finite ι] [CommRing R] [CharZero R] [IsDomain R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

namespace RootPairing

variable {P : RootPairing ι R M N} [P.IsCrystallographic] {i j : ι}

lemma setOf_root_add_zsmul_eq_Icc_of_linearIndependent
    (h : LinearIndependent R ![P.root i, P.root j]) :
    ∃ᵉ (q ≤ 0) (p ≥ 0), {z : ℤ | P.root j + z • P.root i ∈ range P.root} = Icc q p := by
  replace h := LinearIndependent.pair_iff.mp <| h.restrict_scalars' ℤ
  set S : Set ℤ := {z | P.root j + z • P.root i ∈ range P.root} with S_def
  have hS₀ : 0 ∈ S := by simp [S]
  have h_fin : S.Finite := by
    suffices Injective (fun z : S ↦ z.property.choose) from Finite.of_injective _ this
    intro ⟨z, hz⟩ ⟨z', hz'⟩ hzz
    have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
    have : IsAddTorsionFree M := .of_isTorsionFree R M
    have : z • P.root i = z' • P.root i := by
      rwa [← add_right_inj (P.root j), ← hz.choose_spec, ← hz'.choose_spec, P.root.injective.eq_iff]
    exact Subtype.ext <| smul_left_injective ℤ (P.ne_zero i) this
  have h_ne : S.Nonempty := ⟨0, by simp [S_def]⟩
  refine ⟨sInf S, csInf_le h_fin.bddBelow hS₀, sSup S, le_csSup h_fin.bddAbove hS₀,
    (h_ne.eq_Icc_iff_int h_fin.bddBelow h_fin.bddAbove).mpr fun r ⟨k, hk⟩ s ⟨l, hl⟩ hrs ↦ ?_⟩
  by_contra! contra
  have hki_notMem : P.root k + P.root i ∉ range P.root := by
    replace hk : P.root k + P.root i = P.root j + (r + 1) • P.root i := by rw [hk]; module
    replace contra : r + 1 ∉ S := hrs.notMem_of_mem_left <| by simp [contra]
    simpa only [hk, S_def, mem_setOf_eq, S] using contra
  have hki_ne : P.root k ≠ -P.root i := by
    rw [hk]
    contrapose! h
    replace h : r • P.root i = - P.root j - P.root i := by rw [← sub_eq_of_eq_add h.symm]; module
    exact ⟨r + 1, 1, by simp [add_smul, h], by lia⟩
  have hli_notMem : P.root l - P.root i ∉ range P.root := by
    replace hl : P.root l - P.root i = P.root j + (s - 1) • P.root i := by rw [hl]; module
    replace contra : s - 1 ∉ S := hrs.notMem_of_mem_left <| by simp [lt_sub_right_of_add_lt contra]
    simpa only [hl, S_def, mem_setOf_eq, S] using contra
  have hli_ne : P.root l ≠ P.root i := by
    rw [hl]
    contrapose! h
    replace h : s • P.root i = P.root i - P.root j := by rw [← sub_eq_of_eq_add h.symm]; module
    exact ⟨s - 1, 1, by simp [sub_smul, h], by lia⟩
  have h₁ : 0 ≤ P.pairingIn ℤ k i := by
    have := P.root_add_root_mem_of_pairingIn_neg (i := k) (j := i)
    contrapose! this
    exact ⟨this, hki_ne, hki_notMem⟩
  have h₂ : P.pairingIn ℤ k i = P.pairingIn ℤ j i + r * 2 := by
    apply algebraMap_injective ℤ R
    rw [algebraMap_pairingIn, map_add, map_mul, algebraMap_pairingIn, ← root_coroot'_eq_pairing, hk]
    simp
  have h₃ : P.pairingIn ℤ l i ≤ 0 := by
    have := P.root_sub_root_mem_of_pairingIn_pos (i := l) (j := i)
    contrapose! this
    exact ⟨this, fun x ↦ hli_ne (congrArg P.root x), hli_notMem⟩
  have h₄ : P.pairingIn ℤ l i = P.pairingIn ℤ j i + s * 2 := by
    apply algebraMap_injective ℤ R
    rw [algebraMap_pairingIn, map_add, map_mul, algebraMap_pairingIn, ← root_coroot'_eq_pairing, hl]
    simp
  lia

variable (i j)

open scoped Classical in

def chainTopCoeff : ℕ :=
  if h : LinearIndependent R ![P.root i, P.root j]
    then (P.setOf_root_add_zsmul_eq_Icc_of_linearIndependent h).choose_spec.2.choose.toNat
    else 0

open scoped Classical in

def chainBotCoeff : ℕ :=
  if h : LinearIndependent R ![P.root i, P.root j]
    then (-(P.setOf_root_add_zsmul_eq_Icc_of_linearIndependent h).choose).toNat
    else 0

variable {i j}

lemma chainTopCoeff_of_not_linearIndependent (h : ¬ LinearIndependent R ![P.root i, P.root j]) :
    P.chainTopCoeff i j = 0 := by
  simp only [chainTopCoeff, h, reduceDIte]

lemma chainBotCoeff_of_not_linearIndependent (h : ¬ LinearIndependent R ![P.root i, P.root j]) :
    P.chainBotCoeff i j = 0 := by
  simp only [chainBotCoeff, h, reduceDIte]

variable (h : LinearIndependent R ![P.root i, P.root j])

include h

lemma root_add_nsmul_mem_range_iff_le_chainTopCoeff {n : ℕ} :
    P.root j + n • P.root i ∈ range P.root ↔ n ≤ P.chainTopCoeff i j := by
  set S : Set ℤ := {z | P.root j + z • P.root i ∈ range P.root} with S_def
  suffices (n : ℤ) ∈ S ↔ n ≤ P.chainTopCoeff i j by
    simpa only [S_def, mem_setOf_eq, natCast_zsmul] using this
  have aux : P.chainTopCoeff i j =
      (P.setOf_root_add_zsmul_eq_Icc_of_linearIndependent h).choose_spec.2.choose.toNat := by
    simp [chainTopCoeff, h]
  obtain ⟨hp, h₂ : S = _⟩ :=
    (P.setOf_root_add_zsmul_eq_Icc_of_linearIndependent h).choose_spec.2.choose_spec
  rw [aux, h₂, mem_Icc]
  have := (P.setOf_root_add_zsmul_eq_Icc_of_linearIndependent h).choose_spec.1
  lia

lemma root_sub_nsmul_mem_range_iff_le_chainBotCoeff {n : ℕ} :
    P.root j - n • P.root i ∈ range P.root ↔ n ≤ P.chainBotCoeff i j := by
  set S : Set ℤ := {z | P.root j + z • P.root i ∈ range P.root} with S_def
  suffices -(n : ℤ) ∈ S ↔ n ≤ P.chainBotCoeff i j by
    simpa only [S_def, mem_setOf_eq, neg_smul, natCast_zsmul, ← sub_eq_add_neg] using this
  have aux : P.chainBotCoeff i j =
      (-(P.setOf_root_add_zsmul_eq_Icc_of_linearIndependent h).choose).toNat := by
    simp [chainBotCoeff, h]
  obtain ⟨hq, p, hp, h₂ : S = _⟩ :=
    (P.setOf_root_add_zsmul_eq_Icc_of_linearIndependent h).choose_spec
  rw [aux, h₂, mem_Icc]
  lia

lemma Iic_chainTopCoeff_eq :
    Iic (P.chainTopCoeff i j) = {k | P.root j + k • P.root i ∈ range P.root} := by
  ext; simp [← P.root_add_nsmul_mem_range_iff_le_chainTopCoeff h]

lemma Iic_chainBotCoeff_eq :
    Iic (P.chainBotCoeff i j) = {k | P.root j - k • P.root i ∈ range P.root} := by
  ext; simp [← P.root_sub_nsmul_mem_range_iff_le_chainBotCoeff h]

omit h in

lemma one_le_chainTopCoeff_of_root_add_mem [P.IsReduced] (h : P.root i + P.root j ∈ range P.root) :
    1 ≤ P.chainTopCoeff i j := by
  have h' := P.linearIndependent_of_add_mem_range_root' h
  rwa [← root_add_nsmul_mem_range_iff_le_chainTopCoeff h', one_smul, add_comm]

omit h in

lemma one_le_chainBotCoeff_of_root_add_mem [P.IsReduced] (h : P.root i - P.root j ∈ range P.root) :
    1 ≤ P.chainBotCoeff i j := by
  have h' := P.linearIndependent_of_sub_mem_range_root' h
  rwa [← root_sub_nsmul_mem_range_iff_le_chainBotCoeff h', one_smul, ← neg_mem_range_root_iff,
    neg_sub]

lemma root_add_zsmul_mem_range_iff {z : ℤ} :
    P.root j + z • P.root i ∈ range P.root ↔
      z ∈ Icc (-P.chainBotCoeff i j : ℤ) (P.chainTopCoeff i j) := by
  rcases z.eq_nat_or_neg with ⟨n, rfl | rfl⟩
  · simp [P.root_add_nsmul_mem_range_iff_le_chainTopCoeff h]
  · simp [P.root_sub_nsmul_mem_range_iff_le_chainBotCoeff h, ← sub_eq_add_neg]

lemma root_sub_zsmul_mem_range_iff {z : ℤ} :
    P.root j - z • P.root i ∈ range P.root ↔
      z ∈ Icc (-P.chainTopCoeff i j : ℤ) (P.chainBotCoeff i j) := by
  rw [sub_eq_add_neg, ← neg_smul, P.root_add_zsmul_mem_range_iff h, mem_Icc, mem_Icc]
  grind

lemma setOf_root_add_zsmul_mem_eq_Icc :
    {k : ℤ | P.root j + k • P.root i ∈ range P.root} =
      Icc (-P.chainBotCoeff i j : ℤ) (P.chainTopCoeff i j) := by
  ext; simp [← P.root_add_zsmul_mem_range_iff h]

lemma setOf_root_sub_zsmul_mem_eq_Icc :
    {k : ℤ | P.root j - k • P.root i ∈ range P.root} =
      Icc (-P.chainTopCoeff i j : ℤ) (P.chainBotCoeff i j) := by
  ext; rw [← root_sub_zsmul_mem_range_iff h, mem_setOf_eq]

lemma chainTopCoeff_eq_sSup :
    P.chainTopCoeff i j = sSup {k | P.root j + k • P.root i ∈ range P.root} := by
  rw [← Iic_chainTopCoeff_eq h, csSup_Iic]

lemma chainBotCoeff_eq_sSup :
    P.chainBotCoeff i j = sSup {k | P.root j - k • P.root i ∈ range P.root} := by
  rw [← Iic_chainBotCoeff_eq h, csSup_Iic]

lemma coe_chainTopCoeff_eq_sSup :
    P.chainTopCoeff i j = sSup {k : ℤ | P.root j + k • P.root i ∈ range P.root} := by
  rw [setOf_root_add_zsmul_mem_eq_Icc h]
  simp

lemma coe_chainBotCoeff_eq_sSup :
    P.chainBotCoeff i j = sSup {k : ℤ | P.root j - k • P.root i ∈ range P.root} := by
  rw [setOf_root_sub_zsmul_mem_eq_Icc h]
  simp

omit h

private lemma chainCoeff_reflectionPerm_left_aux :
    letI := P.indexNeg
    Icc (-P.chainTopCoeff i j : ℤ) (P.chainBotCoeff i j) =
      Icc (-P.chainBotCoeff (-i) j : ℤ) (P.chainTopCoeff (-i) j) := by
  letI := P.indexNeg
  by_cases h : LinearIndependent R ![P.root i, P.root j]
  · have h' : LinearIndependent R ![P.root (-i), P.root j] := by simpa
    ext z
    rw [← P.root_add_zsmul_mem_range_iff h', indexNeg_neg, root_reflectionPerm, mem_Icc,
      reflection_apply_self, smul_neg, ← neg_smul, P.root_add_zsmul_mem_range_iff h, mem_Icc]
    grind
  · have h' : ¬ LinearIndependent R ![P.root (-i), P.root j] := by simpa
    simp only [chainTopCoeff_of_not_linearIndependent h, chainTopCoeff_of_not_linearIndependent h',
      chainBotCoeff_of_not_linearIndependent h, chainBotCoeff_of_not_linearIndependent h']

private lemma chainCoeff_reflectionPerm_right_aux :
    letI := P.indexNeg
    Icc (-P.chainTopCoeff i j : ℤ) (P.chainBotCoeff i j) =
      Icc (-P.chainBotCoeff i (-j) : ℤ) (P.chainTopCoeff i (-j)) := by
  letI := P.indexNeg
  by_cases h : LinearIndependent R ![P.root i, P.root j]
  · have h' : LinearIndependent R ![P.root i, P.root (-j)] := by simpa
    ext z
    rw [← P.root_add_zsmul_mem_range_iff h', indexNeg_neg, root_reflectionPerm, mem_Icc,
      reflection_apply_self, ← sub_neg_eq_add, ← neg_sub', neg_mem_range_root_iff,
      P.root_sub_zsmul_mem_range_iff h, mem_Icc]
  · have h' : ¬ LinearIndependent R ![P.root i, P.root (-j)] := by simpa
    simp only [chainTopCoeff_of_not_linearIndependent h, chainTopCoeff_of_not_linearIndependent h',
      chainBotCoeff_of_not_linearIndependent h, chainBotCoeff_of_not_linearIndependent h']
