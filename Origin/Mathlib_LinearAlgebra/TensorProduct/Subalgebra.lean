/-
Extracted from LinearAlgebra/TensorProduct/Subalgebra.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Some results on tensor product of subalgebras

## Linear maps induced by multiplication for subalgebras

Let `R` be a commutative ring, `S` be a commutative `R`-algebra.
Let `A` and `B` be `R`-subalgebras in `S` (`Subalgebra R S`). We define some linear maps
induced by the multiplication in `S`, which are
mainly used in the definition of linearly disjointness.

- `Subalgebra.mulMap`: the natural `R`-algebra homomorphism `A ⊗[R] B →ₐ[R] S`
  induced by the multiplication in `S`, whose image is `A ⊔ B` (`Subalgebra.mulMap_range`).

- `Subalgebra.mulMap'`: the natural `R`-algebra homomorphism `A ⊗[R] B →ₗ[R] A ⊔ B`
  induced by multiplication in `S`, which is surjective (`Subalgebra.mulMap'_surjective`).

- `Subalgebra.lTensorBot`, `Subalgebra.rTensorBot`: the natural isomorphism of `R`-algebras between
  `i(R) ⊗[R] A` and `A`, resp. `A ⊗[R] i(R)` and `A`, induced by multiplication in `S`,
  here `i : R → S` is the structure map. They generalize `Algebra.TensorProduct.lid`
  and `Algebra.TensorProduct.rid`, as `i(R)` is not necessarily isomorphic to `R`.

  They are `Subalgebra` versions of `Submodule.lTensorOne` and `Submodule.rTensorOne`.

-/

open scoped TensorProduct

open Module

noncomputable section

variable {R S T : Type*}

section Semiring

variable [CommSemiring R] [Semiring S] [Algebra R S] [Semiring T] [Algebra R T]

namespace Subalgebra

variable (A : Subalgebra R S)

def lTensorBot : (⊥ : Subalgebra R S) ⊗[R] A ≃ₐ[R] A := by
  refine Algebra.TensorProduct.algEquivOfLinearEquivTensorProduct (toSubmodule A).lTensorOne ?_ ?_
  · rintro x y a b
    obtain ⟨x', hx⟩ := Algebra.mem_bot.1 x.2
    replace hx : algebraMap R _ x' = x := Subtype.val_injective hx
    obtain ⟨y', hy⟩ := Algebra.mem_bot.1 y.2
    replace hy : algebraMap R _ y' = y := Subtype.val_injective hy
    rw [← hx, ← hy, ← map_mul]
    erw [(toSubmodule A).lTensorOne_tmul x' a,
      (toSubmodule A).lTensorOne_tmul y' b,
      (toSubmodule A).lTensorOne_tmul (x' * y') (a * b)]
    rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_smul, mul_comm x' y']
  · exact Submodule.lTensorOne_one_tmul _

variable {A}
