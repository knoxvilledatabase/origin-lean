/-
Extracted from LinearAlgebra/Matrix/Determinant/TotallyUnimodular.lean
Genuine: 9 of 9 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Totally unimodular matrices

This file defines totally unimodular matrices and provides basic API for them.

## Main definitions

- `Matrix.IsTotallyUnimodular`: a matrix is totally unimodular iff every square submatrix
  (not necessarily contiguous) has determinant `0` or `1` or `-1`.

## Main results

- `Matrix.isTotallyUnimodular_iff`: a matrix is totally unimodular iff every square submatrix
  (possibly with repeated rows and/or repeated columns) has determinant `0` or `1` or `-1`.
- `Matrix.IsTotallyUnimodular.apply`: entry in a totally unimodular matrix is `0` or `1` or `-1`.

-/

namespace Matrix

variable {m m' n n' R : Type*} [CommRing R]

def IsTotallyUnimodular (A : Matrix m n R) : Prop :=
  ∀ k : ℕ, ∀ f : Fin k → m, ∀ g : Fin k → n, f.Injective → g.Injective →
    (A.submatrix f g).det ∈ Set.range SignType.cast

lemma isTotallyUnimodular_iff (A : Matrix m n R) : A.IsTotallyUnimodular ↔
    ∀ k : ℕ, ∀ f : Fin k → m, ∀ g : Fin k → n,
      (A.submatrix f g).det ∈ Set.range SignType.cast := by
  constructor <;> intro hA
  · intro k f g
    by_cases hfg : f.Injective ∧ g.Injective
    · exact hA k f g hfg.1 hfg.2
    · use 0
      rw [SignType.coe_zero, eq_comm]
      simp_rw [not_and_or, Function.not_injective_iff] at hfg
      obtain ⟨i, j, hfij, hij⟩ | ⟨i, j, hgij, hij⟩ := hfg
      · rw [← det_transpose, transpose_submatrix]
        apply det_zero_of_column_eq hij.symm
        simp [hfij]
      · apply det_zero_of_column_eq hij
        simp [hgij]
  · intro _ _ _ _ _
    apply hA

lemma isTotallyUnimodular_iff_fintype.{w} (A : Matrix m n R) : A.IsTotallyUnimodular ↔
    ∀ (ι : Type w) [Fintype ι] [DecidableEq ι], ∀ f : ι → m, ∀ g : ι → n,
      (A.submatrix f g).det ∈ Set.range SignType.cast := by
  rw [isTotallyUnimodular_iff]
  constructor
  · intro hA ι _ _ f g
    specialize hA (Fintype.card ι) (f ∘ (Fintype.equivFin ι).symm) (g ∘ (Fintype.equivFin ι).symm)
    rwa [← submatrix_submatrix, det_submatrix_equiv_self] at hA
  · intro hA k f g
    specialize hA (ULift (Fin k)) (f ∘ Equiv.ulift) (g ∘ Equiv.ulift)
    rwa [← submatrix_submatrix, det_submatrix_equiv_self] at hA

lemma IsTotallyUnimodular.apply {A : Matrix m n R} (hA : A.IsTotallyUnimodular) (i : m) (j : n) :
    A i j ∈ Set.range SignType.cast := by
  rw [isTotallyUnimodular_iff] at hA
  simpa using hA 1 (fun _ => i) (fun _ => j)

lemma IsTotallyUnimodular.submatrix {A : Matrix m n R} (f : m' → m) (g : n' → n)
    (hA : A.IsTotallyUnimodular) :
    (A.submatrix f g).IsTotallyUnimodular := by
  simp only [isTotallyUnimodular_iff, submatrix_submatrix] at hA ⊢
  intro _ _ _
  apply hA

lemma IsTotallyUnimodular.transpose {A : Matrix m n R} (hA : A.IsTotallyUnimodular) :
    Aᵀ.IsTotallyUnimodular := by
  simp only [isTotallyUnimodular_iff, ← transpose_submatrix, det_transpose] at hA ⊢
  intro _ _ _
  apply hA

lemma transpose_isTotallyUnimodular_iff (A : Matrix m n R) :
    Aᵀ.IsTotallyUnimodular ↔ A.IsTotallyUnimodular := by
  constructor <;> apply IsTotallyUnimodular.transpose

lemma IsTotallyUnimodular.reindex {A : Matrix m n R} (em : m ≃ m') (en : n ≃ n')
    (hA : A.IsTotallyUnimodular) :
    (A.reindex em en).IsTotallyUnimodular :=
  hA.submatrix _ _

lemma reindex_isTotallyUnimodular (A : Matrix m n R) (em : m ≃ m') (en : n ≃ n') :
    (A.reindex em en).IsTotallyUnimodular ↔ A.IsTotallyUnimodular :=
  ⟨fun hA => by simpa [Equiv.symm_apply_eq] using hA.reindex em.symm en.symm,
   fun hA => hA.reindex _ _⟩
