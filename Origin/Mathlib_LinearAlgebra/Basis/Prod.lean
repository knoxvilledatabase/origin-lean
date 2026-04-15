/-
Extracted from LinearAlgebra/Basis/Prod.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Bases for the product of modules
-/

assert_not_exists Ordinal

noncomputable section

universe u

open Function Set Submodule Finsupp

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {M : Type*} {M' : Type*}

namespace Module.Basis

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
  (b : Basis ι R M)

section Prod

variable (b' : Basis ι' R M')

protected def prod : Basis (ι ⊕ ι') R (M × M') :=
  ofRepr ((b.repr.prodCongr b'.repr).trans (Finsupp.sumFinsuppLEquivProdFinsupp R).symm)
