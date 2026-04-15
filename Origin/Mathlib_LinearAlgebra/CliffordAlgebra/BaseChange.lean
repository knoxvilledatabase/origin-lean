/-
Extracted from LinearAlgebra/CliffordAlgebra/BaseChange.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The base change of a clifford algebra

In this file we show the isomorphism

* `CliffordAlgebra.equivBaseChange A Q` :
  `CliffordAlgebra (Q.baseChange A) ≃ₐ[A] (A ⊗[R] CliffordAlgebra Q)`
  with forward direction `CliffordAlgebra.toBaseChange A Q` and reverse direction
  `CliffordAlgebra.ofBaseChange A Q`.

This covers a more general case of the complexification of clifford algebras (as described in §2.2
of https://empg.maths.ed.ac.uk/Activities/Spin/Lecture2.pdf), where ℂ and ℝ are replaced by an
`R`-algebra `A` (where `2 : R` is invertible).

We show the additional results:

* `CliffordAlgebra.toBaseChange_ι`: the effect of base-changing pure vectors.
* `CliffordAlgebra.ofBaseChange_tmul_ι`: the effect of un-base-changing a tensor of a pure vectors.
* `CliffordAlgebra.toBaseChange_involute`: the effect of base-changing an involution.
* `CliffordAlgebra.toBaseChange_reverse`: the effect of base-changing a reversal.
-/

variable {R A V : Type*}

variable [CommRing R] [CommRing A] [AddCommGroup V]

variable [Algebra R A] [Module R V]

variable [Invertible (2 : R)]

open scoped TensorProduct

namespace CliffordAlgebra

variable (A)

set_option backward.isDefEq.respectTransparency false in

def ofBaseChangeAux (Q : QuadraticForm R V) :
    CliffordAlgebra Q →ₐ[R] CliffordAlgebra (Q.baseChange A) :=
  CliffordAlgebra.lift Q <| by
    refine ⟨(ι (Q.baseChange A)).restrictScalars R ∘ₗ TensorProduct.mk R A V 1, fun v => ?_⟩
    refine (CliffordAlgebra.ι_sq_scalar (Q.baseChange A) (1 ⊗ₜ v)).trans ?_
    rw [QuadraticForm.baseChange_tmul, one_mul, ← Algebra.algebraMap_eq_smul_one,
      ← IsScalarTower.algebraMap_apply]
