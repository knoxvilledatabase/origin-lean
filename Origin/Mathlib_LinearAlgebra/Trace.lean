/-
Extracted from LinearAlgebra/Trace.lean
Genuine: 5 of 6 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Trace of a linear map

This file defines the trace of a linear map.

See also `Mathlib/LinearAlgebra/Matrix/Trace.lean` for the trace of a matrix.

## Tags

linear map, trace, diagonal
-/

noncomputable section

universe u v w

namespace LinearMap

open scoped Matrix

open Module TensorProduct

variable (R : Type u) [CommSemiring R] {M : Type v} [AddCommMonoid M] [Module R M]

variable {ι : Type w} [DecidableEq ι] [Fintype ι]

variable {κ : Type*} [DecidableEq κ] [Fintype κ]

variable (b : Basis ι R M) (c : Basis κ R M)

def traceAux : (M →ₗ[R] M) →ₗ[R] R :=
  Matrix.traceLinearMap ι R R ∘ₗ ↑(LinearMap.toMatrix b b)

theorem traceAux_eq : traceAux R b = traceAux R c :=
  LinearMap.ext fun f =>
    calc
      Matrix.trace (LinearMap.toMatrix b b f) =
          Matrix.trace (LinearMap.toMatrix b b ((LinearMap.id.comp f).comp LinearMap.id)) := by
        rw [LinearMap.id_comp, LinearMap.comp_id]
      _ = Matrix.trace (LinearMap.toMatrix c b LinearMap.id * LinearMap.toMatrix c c f *
          LinearMap.toMatrix b c LinearMap.id) := by
        rw [LinearMap.toMatrix_comp _ c, LinearMap.toMatrix_comp _ c]
      _ = Matrix.trace (LinearMap.toMatrix c c f * LinearMap.toMatrix b c LinearMap.id *
          LinearMap.toMatrix c b LinearMap.id) := by
        rw [Matrix.mul_assoc, Matrix.trace_mul_comm]
      _ = Matrix.trace (LinearMap.toMatrix c c ((f.comp LinearMap.id).comp LinearMap.id)) := by
        rw [LinearMap.toMatrix_comp _ b, LinearMap.toMatrix_comp _ c]
      _ = Matrix.trace (LinearMap.toMatrix c c f) := by rw [LinearMap.comp_id, LinearMap.comp_id]

variable (M) in

open Classical in

def trace : (M →ₗ[R] M) →ₗ[R] R :=
  if H : ∃ s : Finset M, Nonempty (Basis s R M) then traceAux R H.choose_spec.some else 0

open Classical in

theorem trace_eq_matrix_trace_of_finset {s : Finset M} (b : Basis s R M) (f : M →ₗ[R] M) :
    trace R M f = Matrix.trace (LinearMap.toMatrix b b f) := by
  have : ∃ s : Finset M, Nonempty (Basis s R M) := ⟨s, ⟨b⟩⟩
  rw [trace, dif_pos this, ← traceAux_def]
  congr 1
  apply traceAux_eq

theorem trace_eq_matrix_trace (f : M →ₗ[R] M) :
    trace R M f = Matrix.trace (LinearMap.toMatrix b b f) := by
  classical
  rw [trace_eq_matrix_trace_of_finset R b.reindexFinsetRange, ← traceAux_def, ← traceAux_def,
    traceAux_eq R b b.reindexFinsetRange]

variable {R} in
