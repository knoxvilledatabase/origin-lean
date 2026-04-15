/-
Extracted from Data/Matrix/ColumnRowPartitioned.lean
Genuine: 6 of 6 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! # Block Matrices from Rows and Columns

This file provides the basic definitions of matrices composed from columns and rows.
The concatenation of two matrices with the same row indices can be expressed as
`A = fromCols A₁ A₂` the concatenation of two matrices with the same column indices
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

def fromCols (B₁ : Matrix m n₁ R) (B₂ : Matrix m n₂ R) : Matrix m (n₁ ⊕ n₂) R :=
  of fun i => Sum.elim (B₁ i) (B₂ i)

def toCols₁ (A : Matrix m (n₁ ⊕ n₂) R) : Matrix m n₁ R := of fun i j => (A i (Sum.inl j))

def toCols₂ (A : Matrix m (n₁ ⊕ n₂) R) : Matrix m n₂ R := of fun i j => (A i (Sum.inr j))

def toRows₁ (A : Matrix (m₁ ⊕ m₂) n R) : Matrix m₁ n R := of fun i j => (A (Sum.inl i) j)

def toRows₂ (A : Matrix (m₁ ⊕ m₂) n R) : Matrix m₂ n R := of fun i j => (A (Sum.inr i) j)
