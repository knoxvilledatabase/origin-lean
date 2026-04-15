/-
Extracted from LinearAlgebra/TensorProduct/Defs.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Tensor product of modules over commutative semirings

This file constructs the tensor product of modules over commutative semirings. Given a semiring `R`
and modules over it `M` and `N`, the standard construction of the tensor product is
`TensorProduct R M N`. It is also a module over `R`.

It comes with a canonical bilinear map
`TensorProduct.mk R M N : M →ₗ[R] N →ₗ[R] TensorProduct R M N`.

## Notation

* This file introduces the notation `M ⊗ N` and `M ⊗[R] N` for the tensor product space
  `TensorProduct R M N`.
* It introduces the notation `m ⊗ₜ n` and `m ⊗ₜ[R] n` for the tensor product of two elements,
  otherwise written as `TensorProduct.tmul R m n`.

## Tags

bilinear, tensor, tensor product
-/

section Semiring

variable {R R₂ R₃ R' R'' : Type*}

variable [CommSemiring R] [CommSemiring R₂] [CommSemiring R₃] [Monoid R'] [Semiring R'']

variable {σ₁₂ : R →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R →+* R₃}

variable {A M N P Q S : Type*}

variable {M₂ M₃ N₂ N₃ P' P₂ P₃ Q' Q₂ Q₃ : Type*}

variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P] [AddCommMonoid Q] [AddCommMonoid S]

variable [AddCommMonoid P'] [AddCommMonoid Q']

variable [AddCommMonoid M₂] [AddCommMonoid N₂] [AddCommMonoid P₂] [AddCommMonoid Q₂]

variable [AddCommMonoid M₃] [AddCommMonoid N₃] [AddCommMonoid P₃] [AddCommMonoid Q₃]

variable [DistribMulAction R' M]

variable [Module R'' M]

variable [Module R M] [Module R N] [Module R S]

variable [Module R P'] [Module R Q']

variable [Module R₂ M₂] [Module R₂ N₂] [Module R₂ P₂] [Module R₂ Q₂]

variable [Module R₃ M₃] [Module R₃ N₃] [Module R₃ P₃] [Module R₃ Q₃]

variable (M N)

namespace TensorProduct

variable (R)

inductive Eqv : FreeAddMonoid (M × N) → FreeAddMonoid (M × N) → Prop
  | of_zero_left : ∀ n : N, Eqv (.of (0, n)) 0
  | of_zero_right : ∀ m : M, Eqv (.of (m, 0)) 0
  | of_add_left : ∀ (m₁ m₂ : M) (n : N), Eqv (.of (m₁, n) + .of (m₂, n)) (.of (m₁ + m₂, n))
  | of_add_right : ∀ (m : M) (n₁ n₂ : N), Eqv (.of (m, n₁) + .of (m, n₂)) (.of (m, n₁ + n₂))
  | of_smul : ∀ (r : R) (m : M) (n : N), Eqv (.of (r • m, n)) (.of (m, r • n))
  | add_comm : ∀ x y, Eqv (x + y) (y + x)

end

end TensorProduct

variable (R) in

def TensorProduct : Type _ :=
  (addConGen (TensorProduct.Eqv R M N)).Quotient

deriving Zero, Add, AddZeroClass, AddSemigroup

set_option quotPrecheck false in
