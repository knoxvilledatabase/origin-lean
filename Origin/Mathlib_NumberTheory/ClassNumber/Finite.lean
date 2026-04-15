/-
Extracted from NumberTheory/ClassNumber/Finite.lean
Genuine: 8 of 9 | Dissolved: 1 | Infrastructure: 0
-/
import Origin.Core

/-!
# Class numbers of global fields
In this file, we use the notion of "admissible absolute value" to prove
finiteness of the class group for number fields and function fields.

## Main definitions
- `ClassGroup.fintypeOfAdmissibleOfAlgebraic`: if `R` has an admissible absolute value,
  its integral closure has a finite class group
-/

open Module Ring

open scoped nonZeroDivisors

namespace ClassGroup

section EuclideanDomain

variable {R S : Type*} (K L : Type*) [EuclideanDomain R] [CommRing S] [IsDomain S]

variable [Field K] [Field L]

variable [Algebra R K] [IsFractionRing R K]

variable [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]

variable [algRL : Algebra R L] [IsScalarTower R K L]

variable [Algebra R S] [Algebra S L]

variable [ist : IsScalarTower R S L]

variable (abv : AbsoluteValue R ℤ)

variable {ι : Type*} [DecidableEq ι] [Fintype ι] (bS : Basis ι R S)

noncomputable def normBound : ℤ :=
  let n := Fintype.card ι
  let i : ι := Nonempty.some bS.index_nonempty
  let m : ℤ :=
    Finset.max'
      (Finset.univ.image fun ijk : ι × ι × ι =>
        abv (Algebra.leftMulMatrix bS (bS ijk.1) ijk.2.1 ijk.2.2))
      ⟨_, Finset.mem_image.mpr ⟨⟨i, i, i⟩, Finset.mem_univ _, rfl⟩⟩
  Nat.factorial n • (n • m) ^ n

theorem normBound_pos : 0 < normBound abv bS := by
  obtain ⟨i, j, k, hijk⟩ : ∃ i j k, Algebra.leftMulMatrix bS (bS i) j k ≠ 0 := by
    by_contra! h
    obtain ⟨i⟩ := bS.index_nonempty
    apply bS.ne_zero i
    apply
      (injective_iff_map_eq_zero (Algebra.leftMulMatrix bS)).mp (Algebra.leftMulMatrix_injective bS)
    ext j k
    simp [h]
  simp only [normBound, Algebra.smul_def, eq_natCast]
  apply mul_pos (Int.natCast_pos.mpr (Nat.factorial_pos _))
  refine pow_pos (mul_pos (Int.natCast_pos.mpr (Fintype.card_pos_iff.mpr ⟨i⟩)) ?_) _
  refine lt_of_lt_of_le (abv.pos hijk) (Finset.le_max' _ _ ?_)
  exact Finset.mem_image.mpr ⟨⟨i, j, k⟩, Finset.mem_univ _, rfl⟩

theorem norm_le (a : S) {y : ℤ} (hy : ∀ k, abv (bS.repr a k) ≤ y) :
    abv (Algebra.norm R a) ≤ normBound abv bS * y ^ Fintype.card ι := by
  conv_lhs => rw [← bS.sum_repr a]
  rw [Algebra.norm_apply, ← LinearMap.det_toMatrix bS]
  simp only [map_sum, map_smul, map_sum, map_smul,
    normBound, smul_mul_assoc, ← mul_pow]
  convert Matrix.det_sum_smul_le Finset.univ _ hy using 3
  · rw [Finset.card_univ, smul_mul_assoc, mul_comm]
  · intro i j k
    apply Finset.le_max'
    exact Finset.mem_image.mpr ⟨⟨i, j, k⟩, Finset.mem_univ _, rfl⟩

theorem norm_lt {T : Type*} [Ring T] [LinearOrder T] [IsStrictOrderedRing T] (a : S) {y : T}
    (hy : ∀ k, (abv (bS.repr a k) : T) < y) :
    (abv (Algebra.norm R a) : T) < normBound abv bS * y ^ Fintype.card ι := by
  obtain ⟨i⟩ := bS.index_nonempty
  have him : (Finset.univ.image fun k => abv (bS.repr a k)).Nonempty :=
    ⟨_, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  set y' : ℤ := Finset.max' _ him with y'_def
  have hy' : ∀ k, abv (bS.repr a k) ≤ y' := by
    intro k
    exact @Finset.le_max' ℤ _ _ _ (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩)
  have : (y' : T) < y := by
    rw [y'_def,
      ← Finset.max'_image (show Monotone (_ : ℤ → T) from fun x y h => Int.cast_le.mpr h)
          _ (him.image _)]
    apply (Finset.max'_lt_iff _ (him.image _)).mpr
    simp only [Finset.mem_image]
    rintro _ ⟨x, ⟨k, -, rfl⟩, rfl⟩
    exact hy k
  have y'_nonneg : 0 ≤ y' := le_trans (abv.nonneg _) (hy' i)
  apply (Int.cast_le.mpr (norm_le abv bS a hy')).trans_lt
  simp only [Int.cast_mul, Int.cast_pow]
  apply mul_lt_mul' le_rfl
  · exact pow_lt_pow_left₀ this (Int.cast_nonneg y'_nonneg) (@Fintype.card_ne_zero _ _ ⟨i⟩)
  · exact pow_nonneg (Int.cast_nonneg y'_nonneg) _
  · exact Int.cast_pos.mpr (normBound_pos abv bS)

-- DISSOLVED: exists_min

section IsAdmissible

variable {abv}

variable (adm : abv.IsAdmissible)

noncomputable def cardM : ℕ :=
  adm.card (normBound abv bS ^ (-1 / Fintype.card ι : ℝ)) ^ Fintype.card ι

variable [Infinite R]

noncomputable def distinctElems : Fin (cardM bS adm).succ ↪ R :=
  Fin.valEmbedding.trans (Infinite.natEmbedding R)

variable [DecidableEq R]

noncomputable def finsetApprox : Finset R :=
  (Finset.univ.image fun xy : _ × _ => distinctElems bS adm xy.1 - distinctElems bS adm xy.2).erase
    0

theorem finsetApprox.zero_notMem : (0 : R) ∉ finsetApprox bS adm :=
  Finset.notMem_erase _ _
