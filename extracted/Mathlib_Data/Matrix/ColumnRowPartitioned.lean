/-
Extracted from Data/Matrix/ColumnRowPartitioned.lean
Genuine: 34 | Conflates: 0 | Dissolved: 0 | Infrastructure: 12
-/
import Origin.Core
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

noncomputable section

/-! # Block Matrices from Rows and Columns

This file provides the basic definitions of matrices composed from columns and rows.
The concatenation of two matrices with the same row indices can be expressed as
`A = fromColumns A₁ A₂` the concatenation of two matrices with the same column indices
can be expressed as `B = fromRows B₁ B₂`.

We then provide a few lemmas that deal with the products of these with each other and
with block matrices

## Tags
column matrices, row matrices, column row block matrices
-/

namespace Matrix

variable {R : Type*}

variable {m m₁ m₂ n n₁ n₂ : Type*}

def fromRows (A₁ : Matrix m₁ n R) (A₂ : Matrix m₂ n R) : Matrix (m₁ ⊕ m₂) n R :=
  of (Sum.elim A₁ A₂)

def fromColumns (B₁ : Matrix m n₁ R) (B₂ : Matrix m n₂ R) : Matrix m (n₁ ⊕ n₂) R :=
  of fun i => Sum.elim (B₁ i) (B₂ i)

def toColumns₁ (A : Matrix m (n₁ ⊕ n₂) R) : Matrix m n₁ R := of fun i j => (A i (Sum.inl j))

def toColumns₂ (A : Matrix m (n₁ ⊕ n₂) R) : Matrix m n₂ R := of fun i j => (A i (Sum.inr j))

def toRows₁ (A : Matrix (m₁ ⊕ m₂) n R) : Matrix m₁ n R := of fun i j => (A (Sum.inl i) j)

def toRows₂ (A : Matrix (m₁ ⊕ m₂) n R) : Matrix m₂ n R := of fun i j => (A (Sum.inr i) j)

@[simp]
lemma fromRows_apply_inl (A₁ : Matrix m₁ n R) (A₂ : Matrix m₂ n R) (i : m₁) (j : n) :
    (fromRows A₁ A₂) (Sum.inl i) j = A₁ i j := rfl

@[simp]
lemma fromRows_apply_inr (A₁ : Matrix m₁ n R) (A₂ : Matrix m₂ n R) (i : m₂) (j : n) :
    (fromRows A₁ A₂) (Sum.inr i) j = A₂ i j := rfl

@[simp]
lemma fromColumns_apply_inl (A₁ : Matrix m n₁ R) (A₂ : Matrix m n₂ R) (i : m) (j : n₁) :
    (fromColumns A₁ A₂) i (Sum.inl j) = A₁ i j := rfl

@[simp]
lemma fromColumns_apply_inr (A₁ : Matrix m n₁ R) (A₂ : Matrix m n₂ R) (i : m) (j : n₂) :
    (fromColumns A₁ A₂) i (Sum.inr j) = A₂ i j := rfl

@[simp]
lemma toRows₁_apply (A : Matrix (m₁ ⊕ m₂) n R) (i : m₁) (j : n) :
    (toRows₁ A) i j = A (Sum.inl i) j := rfl

@[simp]
lemma toRows₂_apply (A : Matrix (m₁ ⊕ m₂) n R) (i : m₂) (j : n) :
    (toRows₂ A) i j = A (Sum.inr i) j := rfl

@[simp]
lemma toRows₁_fromRows (A₁ : Matrix m₁ n R) (A₂ : Matrix m₂ n R) :
    toRows₁ (fromRows A₁ A₂) = A₁ := rfl

@[simp]
lemma toRows₂_fromRows (A₁ : Matrix m₁ n R) (A₂ : Matrix m₂ n R) :
    toRows₂ (fromRows A₁ A₂) = A₂ := rfl

@[simp]
lemma toColumns₁_apply (A : Matrix m (n₁ ⊕ n₂) R) (i : m) (j : n₁) :
    (toColumns₁ A) i j = A i (Sum.inl j) := rfl

@[simp]
lemma toColumns₂_apply (A : Matrix m (n₁ ⊕ n₂) R) (i : m) (j : n₂) :
    (toColumns₂ A) i j = A i (Sum.inr j) := rfl

@[simp]
lemma toColumns₁_fromColumns (A₁ : Matrix m n₁ R) (A₂ : Matrix m n₂ R) :
    toColumns₁ (fromColumns A₁ A₂) = A₁ := rfl

@[simp]
lemma toColumns₂_fromColumns (A₁ : Matrix m n₁ R) (A₂ : Matrix m n₂ R) :
    toColumns₂ (fromColumns A₁ A₂) = A₂ := rfl

@[simp]
lemma fromColumns_toColumns (A : Matrix m (n₁ ⊕ n₂) R) :
    fromColumns A.toColumns₁ A.toColumns₂ = A := by
  ext i (j | j) <;> simp

@[simp]
lemma fromRows_toRows (A : Matrix (m₁ ⊕ m₂) n R) : fromRows A.toRows₁ A.toRows₂ = A := by
  ext (i | i) j <;> simp

lemma fromRows_inj : Function.Injective2 (@fromRows R m₁ m₂ n) := by
  intros x1 x2 y1 y2
  simp only [funext_iff, ← Matrix.ext_iff]
  aesop

lemma fromColumns_inj : Function.Injective2 (@fromColumns R m n₁ n₂) := by
  intros x1 x2 y1 y2
  simp only [funext_iff, ← Matrix.ext_iff]
  aesop

lemma fromColumns_ext_iff (A₁ : Matrix m n₁ R) (A₂ : Matrix m n₂ R) (B₁ : Matrix m n₁ R)
    (B₂ : Matrix m n₂ R) :
    fromColumns A₁ A₂ = fromColumns B₁ B₂ ↔ A₁ = B₁ ∧ A₂ = B₂ := fromColumns_inj.eq_iff

lemma fromRows_ext_iff (A₁ : Matrix m₁ n R) (A₂ : Matrix m₂ n R) (B₁ : Matrix m₁ n R)
    (B₂ : Matrix m₂ n R) :
    fromRows A₁ A₂ = fromRows B₁ B₂ ↔ A₁ = B₁ ∧ A₂ = B₂ := fromRows_inj.eq_iff

lemma transpose_fromColumns (A₁ : Matrix m n₁ R) (A₂ : Matrix m n₂ R) :
    transpose (fromColumns A₁ A₂) = fromRows (transpose A₁) (transpose A₂) := by
  ext (i | i) j <;> simp

lemma transpose_fromRows (A₁ : Matrix m₁ n R) (A₂ : Matrix m₂ n R) :
    transpose (fromRows A₁ A₂) = fromColumns (transpose A₁) (transpose A₂) := by
  ext i (j | j) <;> simp

section Neg

variable [Neg R]

@[simp]
lemma fromRows_neg (A₁ : Matrix m₁ n R) (A₂ : Matrix m₂ n R) :
    -fromRows A₁ A₂ = fromRows (-A₁) (-A₂) := by
  ext (i | i) j <;> simp

@[simp]
lemma fromColumns_neg (A₁ : Matrix n m₁ R) (A₂ : Matrix n m₂ R) :
    -fromColumns A₁ A₂ = fromColumns (-A₁) (-A₂) := by
  ext i (j | j) <;> simp

end Neg

@[simp]
lemma fromColumns_fromRows_eq_fromBlocks (B₁₁ : Matrix m₁ n₁ R) (B₁₂ : Matrix m₁ n₂ R)
    (B₂₁ : Matrix m₂ n₁ R) (B₂₂ : Matrix m₂ n₂ R) :
    fromColumns (fromRows B₁₁ B₂₁) (fromRows B₁₂ B₂₂) = fromBlocks B₁₁ B₁₂ B₂₁ B₂₂ := by
  ext (_ | _) (_ | _) <;> simp

@[simp]
lemma fromRows_fromColumn_eq_fromBlocks (B₁₁ : Matrix m₁ n₁ R) (B₁₂ : Matrix m₁ n₂ R)
    (B₂₁ : Matrix m₂ n₁ R) (B₂₂ : Matrix m₂ n₂ R) :
    fromRows (fromColumns B₁₁ B₁₂) (fromColumns B₂₁ B₂₂) = fromBlocks B₁₁ B₁₂ B₂₁ B₂₂ := by
  ext (_ | _) (_ | _) <;> simp

section Semiring

variable [Semiring R]

@[simp]
lemma fromRows_mulVec [Fintype n] (A₁ : Matrix m₁ n R) (A₂ : Matrix m₂ n R) (v : n → R) :
    fromRows A₁ A₂ *ᵥ v = Sum.elim (A₁ *ᵥ v) (A₂ *ᵥ v) := by
  ext (_ | _) <;> rfl

@[simp]
lemma vecMul_fromColumns [Fintype m] (B₁ : Matrix m n₁ R) (B₂ : Matrix m n₂ R) (v : m → R) :
    v ᵥ* fromColumns B₁ B₂ = Sum.elim (v ᵥ* B₁) (v ᵥ* B₂) := by
  ext (_ | _) <;> rfl

@[simp]
lemma sum_elim_vecMul_fromRows [Fintype m₁] [Fintype m₂] (B₁ : Matrix m₁ n R) (B₂ : Matrix m₂ n R)
    (v₁ : m₁ → R) (v₂ : m₂ → R) :
    Sum.elim v₁ v₂ ᵥ* fromRows B₁ B₂ = v₁ ᵥ* B₁ + v₂ ᵥ* B₂ := by
  ext
  simp [Matrix.vecMul, fromRows, dotProduct]

@[simp]
lemma fromColumns_mulVec_sum_elim [Fintype n₁] [Fintype n₂]
    (A₁ : Matrix m n₁ R) (A₂ : Matrix m n₂ R) (v₁ : n₁ → R) (v₂ : n₂ → R) :
    fromColumns A₁ A₂ *ᵥ Sum.elim v₁ v₂ = A₁ *ᵥ v₁ + A₂ *ᵥ v₂ := by
  ext
  simp [Matrix.mulVec, fromColumns]

@[simp]
lemma fromRows_mul [Fintype n] (A₁ : Matrix m₁ n R) (A₂ : Matrix m₂ n R) (B : Matrix n m R) :
    fromRows A₁ A₂ * B = fromRows (A₁ * B) (A₂ * B) := by
  ext (_ | _) _ <;> simp [mul_apply]

@[simp]
lemma mul_fromColumns [Fintype n] (A : Matrix m n R) (B₁ : Matrix n n₁ R) (B₂ : Matrix n n₂ R) :
    A * fromColumns B₁ B₂ = fromColumns (A * B₁) (A * B₂) := by
  ext _ (_ | _) <;> simp [mul_apply]

@[simp]
lemma fromRows_zero : fromRows (0 : Matrix m₁ n R) (0 : Matrix m₂ n R) = 0 := by
  ext (_ | _) _ <;> simp

@[simp]
lemma fromColumns_zero : fromColumns (0 : Matrix m n₁ R) (0 : Matrix m n₂ R) = 0 := by
  ext _ (_ | _) <;> simp

lemma fromRows_mul_fromColumns [Fintype n] (A₁ : Matrix m₁ n R) (A₂ : Matrix m₂ n R)
    (B₁ : Matrix n n₁ R) (B₂ : Matrix n n₂ R) :
    (fromRows A₁ A₂) * (fromColumns B₁ B₂) =
      fromBlocks (A₁ * B₁) (A₁ * B₂) (A₂ * B₁) (A₂ * B₂) := by
  ext (_ | _) (_ | _) <;> simp

lemma fromColumns_mul_fromRows [Fintype n₁] [Fintype n₂] (A₁ : Matrix m n₁ R) (A₂ : Matrix m n₂ R)
    (B₁ : Matrix n₁ n R) (B₂ : Matrix n₂ n R) :
    fromColumns A₁ A₂ * fromRows B₁ B₂ = (A₁ * B₁ + A₂ * B₂) := by
  ext
  simp [mul_apply]

lemma fromColumns_mul_fromBlocks [Fintype m₁] [Fintype m₂] (A₁ : Matrix m m₁ R) (A₂ : Matrix m m₂ R)
    (B₁₁ : Matrix m₁ n₁ R) (B₁₂ : Matrix m₁ n₂ R) (B₂₁ : Matrix m₂ n₁ R) (B₂₂ : Matrix m₂ n₂ R) :
    (fromColumns A₁ A₂) * fromBlocks B₁₁ B₁₂ B₂₁ B₂₂ =
      fromColumns (A₁ * B₁₁ + A₂ * B₂₁) (A₁ * B₁₂ + A₂ * B₂₂) := by
  ext _ (_ | _) <;> simp [mul_apply]

lemma fromBlocks_mul_fromRows [Fintype n₁] [Fintype n₂] (A₁ : Matrix n₁ n R) (A₂ : Matrix n₂ n R)
    (B₁₁ : Matrix m₁ n₁ R) (B₁₂ : Matrix m₁ n₂ R) (B₂₁ : Matrix m₂ n₁ R) (B₂₂ : Matrix m₂ n₂ R) :
    fromBlocks B₁₁ B₁₂ B₂₁ B₂₂ * (fromRows A₁ A₂) =
      fromRows (B₁₁ * A₁ + B₁₂ * A₂) (B₂₁ * A₁ + B₂₂ * A₂) := by
  ext (_ | _) _ <;> simp [mul_apply]

end Semiring

section CommRing

variable [CommRing R]

lemma fromColumns_mul_fromRows_eq_one_comm
    [Fintype n₁] [Fintype n₂] [Fintype n] [DecidableEq n] [DecidableEq n₁] [DecidableEq n₂]
    (e : n ≃ n₁ ⊕ n₂)
    (A₁ : Matrix n n₁ R) (A₂ : Matrix n n₂ R) (B₁ : Matrix n₁ n R) (B₂ : Matrix n₂ n R) :
    fromColumns A₁ A₂ * fromRows B₁ B₂ = 1 ↔ fromRows B₁ B₂ * fromColumns A₁ A₂ = 1 :=
  mul_eq_one_comm_of_equiv e

lemma equiv_compl_fromColumns_mul_fromRows_eq_one_comm
    [Fintype n] [DecidableEq n] (p : n → Prop) [DecidablePred p]
    (A₁ : Matrix n {i // p i} R) (A₂ : Matrix n {i // ¬p i} R)
    (B₁ : Matrix {i // p i} n R) (B₂ : Matrix {i // ¬p i} n R) :
    fromColumns A₁ A₂ * fromRows B₁ B₂ = 1 ↔ fromRows B₁ B₂ * fromColumns A₁ A₂ = 1 :=
  fromColumns_mul_fromRows_eq_one_comm (id (Equiv.sumCompl p).symm) A₁ A₂ B₁ B₂

end CommRing

section Star

variable [Star R]

lemma conjTranspose_fromColumns_eq_fromRows_conjTranspose (A₁ : Matrix m n₁ R)
    (A₂ : Matrix m n₂ R) :
    conjTranspose (fromColumns A₁ A₂) = fromRows (conjTranspose A₁) (conjTranspose A₂) := by
  ext (_ | _) _ <;> simp

lemma conjTranspose_fromRows_eq_fromColumns_conjTranspose (A₁ : Matrix m₁ n R)
    (A₂ : Matrix m₂ n R) : conjTranspose (fromRows A₁ A₂) =
      fromColumns (conjTranspose A₁) (conjTranspose A₂) := by
  ext _ (_ | _) <;> simp

end Star

end Matrix
