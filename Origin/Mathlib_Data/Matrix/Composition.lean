/-
Extracted from Data/Matrix/Composition.lean
Genuine: 5 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Data.Matrix.Basic

noncomputable section

/-!
# Composition of matrices

This file shows that Mₙ(Mₘ(R)) ≃ Mₙₘ(R), Mₙ(Rᵒᵖ) ≃ₐ[K] Mₙ(R)ᵒᵖ
and also different levels of equivalence when R is an AddCommMonoid,
Semiring, and Algebra over a CommSemiring K.

## Main results

* `Matrix.comp` is an equivalence between `Matrix I J (Matrix K L R)` and
  `I × K` by `J × L` matrices.
* `Matrix.swap` is an equivalence between `(I × J)` by `(K × L)` matrices and
  `J × I` by `L × K` matrices.

-/

namespace Matrix

variable (I J K L R : Type*)

@[simps]
def comp : Matrix I J (Matrix K L R) ≃ Matrix (I × K) (J × L) R where
  toFun m ik jl := m ik.1 jl.1 ik.2 jl.2
  invFun n i j k l := n (i, k) (j, l)
  left_inv _ := rfl
  right_inv _ := rfl

section AddCommMonoid

variable [AddCommMonoid R]

@[simps!]
def compAddEquiv : Matrix I J (Matrix K L R) ≃+ Matrix (I × K) (J × L) R where
  __ := Matrix.comp I J K L R
  map_add' _ _ := rfl

end AddCommMonoid

section Semiring

variable [Semiring R] [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

@[simps!]
def compRingEquiv : Matrix I I (Matrix J J R) ≃+* Matrix (I × J) (I × J) R where
  __ := Matrix.compAddEquiv I I J J R
  map_mul' _ _ := by ext; exact (Matrix.sum_apply ..).trans <| .symm <| Fintype.sum_prod_type ..

end Semiring

section LinearMap

variable (K : Type*) [CommSemiring K] [AddCommMonoid R] [Module K R]

end LinearMap

section Algebra

variable (K : Type*) [CommSemiring K] [Semiring R] [Fintype I] [Fintype J] [Algebra K R]

variable [DecidableEq I] [DecidableEq J]

@[simps!]
def compAlgEquiv : Matrix I I (Matrix J J R) ≃ₐ[K] Matrix (I × J) (I × J) R where
  __ := Matrix.compRingEquiv I J R
  commutes' c := by
    ext _ _
    simp only [compRingEquiv, compAddEquiv, comp, AddEquiv.toEquiv_eq_coe, RingEquiv.toEquiv_eq_coe,
      Equiv.toFun_as_coe, EquivLike.coe_coe, RingEquiv.coe_mk, AddEquiv.coe_mk, Equiv.coe_fn_mk,
      algebraMap_eq_diagonal]
    rw [Pi.algebraMap_def, Pi.algebraMap_def, Algebra.algebraMap_eq_smul_one',
      Algebra.algebraMap_eq_smul_one', ← diagonal_one, diagonal_apply, diagonal_apply]
    aesop

end Algebra

end Matrix
