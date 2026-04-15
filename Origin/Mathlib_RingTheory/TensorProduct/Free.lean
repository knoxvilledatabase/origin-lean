/-
Extracted from RingTheory/TensorProduct/Free.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Results on bases of tensor products

In the file we construct a basis for the base change of a module to an algebra,
and deduce that `Module.Free` is stable under base change.

## Main declarations

- `Algebra.TensorProduct.basis`: given a basis of a module `M` over a commutative semiring `R`,
  and an `R`-algebra `A`, this provides a basis for `A ⊗[R] M` over `A`.
- `Algebra.TensorProduct.instFree`: if `M` is free, then so is `A ⊗[R] M`.

-/

assert_not_exists Cardinal

open Module

open scoped TensorProduct

namespace Algebra

namespace TensorProduct

variable {R A : Type*}

section Basis

universe uM uι

variable {M : Type uM} {ι : Type uι}

variable [CommSemiring R] [Semiring A] [Algebra R A]

variable [AddCommMonoid M] [Module R M] (b : Basis ι R M)

variable (A) in

noncomputable def basisAux : A ⊗[R] M ≃ₗ[R] ι →₀ A :=
  _root_.TensorProduct.congr (Finsupp.LinearEquiv.finsuppUnique R A PUnit.{uι + 1}).symm b.repr ≪≫ₗ
    (finsuppTensorFinsupp R R A R PUnit ι).trans
      (Finsupp.lcongr (Equiv.uniqueProd ι PUnit) (_root_.TensorProduct.rid R A))

theorem basisAux_tmul (a : A) (m : M) :
    basisAux A b (a ⊗ₜ m) = a • Finsupp.mapRange (algebraMap R A) (map_zero _) (b.repr m) := by
  ext
  simp [basisAux, ← Algebra.commutes, Algebra.smul_def]

theorem basisAux_map_smul (a : A) (x : A ⊗[R] M) : basisAux A b (a • x) = a • basisAux A b x :=
  TensorProduct.induction_on x (by simp)
    (fun x y => by simp only [TensorProduct.smul_tmul', basisAux_tmul, smul_assoc])
    fun x y hx hy => by simp [hx, hy]

variable (A) in

noncomputable def basis : Basis ι A (A ⊗[R] M) where
  repr := { basisAux A b with map_smul' := basisAux_map_smul b }
