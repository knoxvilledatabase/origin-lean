/-
Extracted from LinearAlgebra/Matrix/StdBasis.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Standard basis on matrices

## Main results

* `Basis.matrix`: extend a basis on `M` to the standard basis on `Matrix n m M`
-/

open Module

namespace Module.Basis

variable {ι R M : Type*} (m n : Type*)

variable [Fintype m] [Fintype n] [Semiring R] [AddCommMonoid M] [Module R M]

protected noncomputable def matrix (b : Basis ι R M) :
    Basis (m × n × ι) R (Matrix m n M) :=
  Basis.reindex (Pi.basis fun _ : m => Pi.basis fun _ : n => b)
    ((Equiv.sigmaEquivProd _ _).trans <| .prodCongr (.refl _) (Equiv.sigmaEquivProd _ _))
    |>.map (Matrix.ofLinearEquiv R)

variable {n m}
