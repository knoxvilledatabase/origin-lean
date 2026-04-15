/-
Extracted from LinearAlgebra/StdBasis.lean
Genuine: 3 of 4 | Dissolved: 1 | Infrastructure: 0
-/
import Origin.Core

/-!
# The standard basis

This file defines the standard basis `Pi.basis (s : ∀ j, Basis (ι j) R (M j))`,
which is the `Σ j, ι j`-indexed basis of `Π j, M j`. The basis vectors are given by
`Pi.basis s ⟨j, i⟩ j' = Pi.single j' (s j) i = if j = j' then s i else 0`.

The standard basis on `R^η`, i.e. `η → R` is called `Pi.basisFun`.

To give a concrete example, `Pi.single (i : Fin 3) (1 : R)`
gives the `i`th unit basis vector in `R³`, and `Pi.basisFun R (Fin 3)` proves
this is a basis over `Fin 3 → R`.

## Main definitions

- `Pi.basis s`: given a basis `s i` for each `M i`, the standard basis on `Π i, M i`
- `Pi.basisFun R η`: the standard basis on `R^η`, i.e. `η → R`, given by
  `Pi.basisFun R η i j = Pi.single i 1 j = if i = j then 1 else 0`.
- `Matrix.stdBasis R n m`: the standard basis on `Matrix n m R`, given by
  `Matrix.stdBasis R n m (i, j) i' j' = if (i, j) = (i', j') then 1 else 0`.

-/

open Function LinearMap Module Set Submodule

namespace Pi

variable {ι R M : Type*}

section Module

variable {η : Type*} {ιs : η → Type*} {Ms : η → Type*}

theorem linearIndependent_single [Semiring R] [∀ i, AddCommMonoid (Ms i)] [∀ i, Module R (Ms i)]
    [DecidableEq η] (v : ∀ j, ιs j → Ms j) (hs : ∀ i, LinearIndependent R (v i)) :
    LinearIndependent R fun ji : Σ j, ιs j ↦ Pi.single ji.1 (v ji.1 ji.2) := by
  convert (DFinsupp.linearIndependent_single _ hs).map_injOn _ DFinsupp.injective_pi_lapply.injOn

theorem linearIndependent_single_one (ι R : Type*) [Semiring R] [DecidableEq ι] :
    LinearIndependent R (fun i : ι ↦ Pi.single i (1 : R)) := by
  rw [← linearIndependent_equiv (Equiv.sigmaPUnit ι)]
  exact Pi.linearIndependent_single (fun (_ : ι) (_ : Unit) ↦ (1 : R))
    <| by simp +contextual [Fintype.linearIndependent_iffₛ]

-- DISSOLVED: linearIndependent_single_of_ne_zero

variable [Semiring R] [∀ i, AddCommMonoid (Ms i)] [∀ i, Module R (Ms i)]

section Fintype

variable [Fintype η]

open LinearEquiv

protected noncomputable def basis (s : ∀ j, Basis (ιs j) R (Ms j)) :
    Basis (Σ j, ιs j) R (∀ j, Ms j) :=
  Basis.ofRepr
    ((LinearEquiv.piCongrRight fun j => (s j).repr) ≪≫ₗ
      (Finsupp.sigmaFinsuppLEquivPiFinsupp R).symm)
