/-
Extracted from LinearAlgebra/Dual/Basis.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Bases of dual vector spaces

The dual space of an $R$-module $M$ is the $R$-module of $R$-linear maps $M \to R$.
This file concerns bases on dual vector spaces.

## Main definitions

* Bases:
  * `Basis.toDual` produces the map `M →ₗ[R] Dual R M` associated to a basis for an `R`-module `M`.
  * `Basis.toDualEquiv` is the equivalence `M ≃ₗ[R] Dual R M` associated to a finite basis.
  * `Basis.dualBasis` is a basis for `Dual R M` given a finite basis for `M`.
  * `Module.DualBases e ε` is the proposition that the families `e` of vectors and `ε` of dual
    vectors have the characteristic properties of a basis and a dual.

## Main results

* Bases:
  * `Module.DualBases.basis` and `Module.DualBases.coe_basis`: if `e` and `ε` form a dual pair,
    then `e` is a basis.
  * `Module.DualBases.coe_dualBasis`: if `e` and `ε` form a dual pair,
    then `ε` is a basis.
-/

open Module Dual Submodule LinearMap Function

noncomputable section

namespace Module.Basis

universe u v w uR uM uK uV uι

variable {R : Type uR} {M : Type uM} {K : Type uK} {V : Type uV} {ι : Type uι}

section CommSemiring

variable [CommSemiring R] [AddCommMonoid M] [Module R M] [DecidableEq ι]

variable (b : Basis ι R M)

def toDual : M →ₗ[R] Module.Dual R M :=
  b.constr ℕ fun v => b.constr ℕ fun w => if w = v then (1 : R) else 0

theorem toDual_apply (i j : ι) : b.toDual (b i) (b j) = if i = j then 1 else 0 := by
  rw [toDual, constr_basis b, constr_basis b]
  simp only [eq_comm]
