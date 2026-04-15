/-
Extracted from Analysis/InnerProductSpace/Orientation.lean
Genuine: 7 of 7 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Orientations of real inner product spaces.

This file provides definitions and proves lemmas about orientations of real inner product spaces.

## Main definitions

* `OrthonormalBasis.adjustToOrientation` takes an orthonormal basis and an orientation, and
  returns an orthonormal basis with that orientation: either the original orthonormal basis, or one
  constructed by negating a single (arbitrary) basis vector.
* `Orientation.finOrthonormalBasis` is an orthonormal basis, indexed by `Fin n`, with the given
  orientation.
* `Orientation.volumeForm` is a nonvanishing top-dimensional alternating form on an oriented real
  inner product space, uniquely defined by compatibility with the orientation and inner product
  structure.

## Main theorems

* `Orientation.volumeForm_apply_le` states that the result of applying the volume form to a set of
  `n` vectors, where `n` is the dimension the inner product space, is bounded by the product of the
  lengths of the vectors.
* `Orientation.abs_volumeForm_apply_of_pairwise_orthogonal` states that the result of applying the
  volume form to a set of `n` orthogonal vectors, where `n` is the dimension the inner product
  space, is equal up to sign to the product of the lengths of the vectors.

-/

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

open Module InnerProductSpace

open scoped RealInnerProductSpace

namespace OrthonormalBasis

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (e f : OrthonormalBasis ι ℝ E)
  (x : Orientation ℝ E ι)

theorem det_to_matrix_orthonormalBasis_of_same_orientation
    (h : e.toBasis.orientation = f.toBasis.orientation) : e.toBasis.det f = 1 := by
  apply (e.det_to_matrix_orthonormalBasis_real f).resolve_right
  have : 0 < e.toBasis.det f := by
    rw [e.toBasis.orientation_eq_iff_det_pos] at h
    simpa using h
  linarith

theorem det_to_matrix_orthonormalBasis_of_opposite_orientation
    (h : e.toBasis.orientation ≠ f.toBasis.orientation) : e.toBasis.det f = -1 := by
  contrapose! h
  simp [e.toBasis.orientation_eq_iff_det_pos,
    (e.det_to_matrix_orthonormalBasis_real f).resolve_right h]

variable {e f}

theorem same_orientation_iff_det_eq_det :
    e.toBasis.det = f.toBasis.det ↔ e.toBasis.orientation = f.toBasis.orientation := by
  constructor
  · intro h
    dsimp [Basis.orientation]
    congr
  · intro h
    rw [e.toBasis.det.eq_smul_basis_det f.toBasis]
    simp [e.det_to_matrix_orthonormalBasis_of_same_orientation f h]

variable (e f)

theorem det_eq_neg_det_of_opposite_orientation (h : e.toBasis.orientation ≠ f.toBasis.orientation) :
    e.toBasis.det = -f.toBasis.det := by
  rw [e.toBasis.det.eq_smul_basis_det f.toBasis]
  simp [e.det_to_matrix_orthonormalBasis_of_opposite_orientation f h]

variable [Nonempty ι]

section AdjustToOrientation

theorem orthonormal_adjustToOrientation : Orthonormal ℝ (e.toBasis.adjustToOrientation x) := by
  apply e.orthonormal.orthonormal_of_forall_eq_or_eq_neg
  simpa using e.toBasis.adjustToOrientation_apply_eq_or_eq_neg x

def adjustToOrientation : OrthonormalBasis ι ℝ E :=
  (e.toBasis.adjustToOrientation x).toOrthonormalBasis (e.orthonormal_adjustToOrientation x)

theorem toBasis_adjustToOrientation :
    (e.adjustToOrientation x).toBasis = e.toBasis.adjustToOrientation x :=
  (e.toBasis.adjustToOrientation x).toBasis_toOrthonormalBasis _
