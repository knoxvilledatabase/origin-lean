/-
Extracted from LinearAlgebra/Matrix/WithConv.lean
Genuine: 2 of 36 | Dissolved: 0 | Infrastructure: 34
-/
import Origin.Core

/-! # The convolutive star ring on matrices

In this file, we provide the star algebra instance on `WithConv (Matrix m n R)` given by
the Hadamard product and intrinsic star (i.e., the star of each element in the matrix). -/

variable {m n α β : Type*}

open Matrix WithConv

-- INSTANCE (free from Core): [Mul

attribute [local simp] convMul_def

-- INSTANCE (free from Core): [Semigroup

-- INSTANCE (free from Core): [NonUnitalNonAssocSemiring

-- INSTANCE (free from Core): [CommMagma

-- INSTANCE (free from Core): [One

attribute [local simp] convOne_def

-- INSTANCE (free from Core): [MulOneClass

-- INSTANCE (free from Core): [Monoid

-- INSTANCE (free from Core): [CommMonoid

-- INSTANCE (free from Core): [NonAssocSemiring

-- INSTANCE (free from Core): [NonUnitalSemiring

-- INSTANCE (free from Core): [NonUnitalNonAssocCommSemiring

-- INSTANCE (free from Core): [NonUnitalCommSemiring

-- INSTANCE (free from Core): [NonAssocCommSemiring

-- INSTANCE (free from Core): [Semiring

-- INSTANCE (free from Core): [CommSemiring

-- INSTANCE (free from Core): [NonUnitalNonAssocRing

-- INSTANCE (free from Core): [NonUnitalNonAssocCommRing

-- INSTANCE (free from Core): [NonUnitalRing

-- INSTANCE (free from Core): [NonUnitalCommRing

-- INSTANCE (free from Core): [NonAssocRing

-- INSTANCE (free from Core): [NonAssocCommRing

-- INSTANCE (free from Core): [Ring

-- INSTANCE (free from Core): [CommRing

-- INSTANCE (free from Core): [Star

attribute [local simp] intrinsicStar_def

-- INSTANCE (free from Core): [InvolutiveStar

-- INSTANCE (free from Core): [AddMonoid

-- INSTANCE (free from Core): [Mul

-- INSTANCE (free from Core): [NonUnitalNonAssocSemiring

-- INSTANCE (free from Core): [Monoid

-- INSTANCE (free from Core): [Monoid

-- INSTANCE (free from Core): [CommSemiring

theorem Matrix.WithConv.IsIdempotentElem.isSelfAdjoint [Semiring α] [IsLeftCancelMulZero α]
    [StarRing α] {f : WithConv (Matrix m n α)} (hf : IsIdempotentElem f) : IsSelfAdjoint f := by
  simp_rw [IsIdempotentElem, WithConv.ext_iff, ← Matrix.ext_iff, convMul_def, hadamard_apply,
    ← isIdempotentElem_iff, IsIdempotentElem.iff_eq_zero_or_one] at hf
  rw [IsSelfAdjoint, WithConv.ext_iff]
  ext i j
  obtain (h | h) := hf i j <;> simp_all

section toLin'

variable [CommSemiring α] [StarRing α] [Fintype n] [DecidableEq n]

namespace WithConv

variable (m n α) in

def matrixToLin'StarAlgEquiv :
    WithConv (Matrix m n α) ≃⋆ₐ[α] WithConv ((n → α) →ₗ[α] m → α) where
  __ := congrLinearEquiv toLin'
  map_mul' _ _ := by ext; simp
  map_star' _ := by classical exact Matrix.intrinsicStar_toLin' _ |>.symm
