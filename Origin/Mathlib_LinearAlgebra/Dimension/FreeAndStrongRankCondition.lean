/-
Extracted from LinearAlgebra/Dimension/FreeAndStrongRankCondition.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Some results on free modules over rings satisfying strong rank condition

This file contains some results on free modules over rings satisfying strong rank condition.
Most of them are generalized from the same result assuming the base ring being a division ring,
and are moved from the files `Mathlib/LinearAlgebra/Dimension/DivisionRing.lean`
and `Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean`.

-/

open Cardinal Module Module Set Submodule

universe u v

section Module

variable {K : Type u} {V : Type v} [Ring K] [StrongRankCondition K] [AddCommGroup V] [Module K V]

noncomputable def Basis.ofRankEqZero [Module.Free K V] {ι : Type*} [IsEmpty ι]
    (hV : Module.rank K V = 0) : Basis ι K V :=
  haveI : Subsingleton V := by
    obtain ⟨_, b⟩ := Module.Free.exists_basis (R := K) (M := V)
    haveI := mk_eq_zero_iff.1 (hV ▸ b.mk_eq_rank'')
    exact b.repr.toEquiv.subsingleton
  Basis.empty _
