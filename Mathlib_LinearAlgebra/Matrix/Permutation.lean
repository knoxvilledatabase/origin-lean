/-
Extracted from LinearAlgebra/Matrix/Permutation.lean
Genuine: 3 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Data.Matrix.PEquiv
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace

noncomputable section

/-!
# Permutation matrices

This file defines the matrix associated with a permutation

## Main definitions

 - `Equiv.Perm.permMatrix`: the permutation matrix associated with an `Equiv.Perm`

## Main results

 - `Matrix.det_permutation`: the determinant is the sign of the permutation
 - `Matrix.trace_permutation`: the trace is the number of fixed points of the permutation

-/

open Equiv

variable {n R : Type*} [DecidableEq n] [Fintype n] (σ : Perm n)

variable (R) in

abbrev Equiv.Perm.permMatrix [Zero R] [One R] : Matrix n n R :=
  σ.toPEquiv.toMatrix

namespace Matrix

@[simp]
theorem det_permutation [CommRing R] : det (σ.permMatrix R) = Perm.sign σ := by
  rw [← Matrix.mul_one (σ.permMatrix R), PEquiv.toPEquiv_mul_matrix,
    det_permute, det_one, mul_one]

theorem trace_permutation [AddCommMonoidWithOne R] :
    trace (σ.permMatrix R) = (Function.fixedPoints σ).ncard := by
  delta trace
  simp [toPEquiv_apply, ← Set.ncard_coe_Finset, Function.fixedPoints, Function.IsFixedPt]

end Matrix
