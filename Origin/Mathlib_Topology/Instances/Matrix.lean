/-
Extracted from Topology/Instances/Matrix.lean
Genuine: 2 of 10 | Dissolved: 0 | Infrastructure: 8
-/
import Origin.Core

/-!
# Topological properties of matrices

This file is a place to collect topological results about matrices.

## Main definitions:

* `Matrix.topologicalRing`: square matrices form a topological ring

## Main results

* Sets of matrices:
  * `IsOpen.matrix`: the set of finite matrices with entries in an open set
    is itself an open set.
  * `IsCompact.matrix`: the set of matrices with entries in a compact set
    is itself a compact set.
* Continuity:
  * `Continuous.matrix_det`: the determinant is continuous over a topological ring.
  * `Continuous.matrix_adjugate`: the adjugate is continuous over a topological ring.
* Infinite sums
  * `Matrix.transpose_tsum`: transpose commutes with infinite sums
  * `Matrix.diagonal_tsum`: diagonal commutes with infinite sums
  * `Matrix.blockDiagonal_tsum`: block diagonal commutes with infinite sums
  * `Matrix.blockDiagonal'_tsum`: non-uniform block diagonal commutes with infinite sums
-/

assert_not_exists Matrix.GeneralLinearGroup Matrix.SpecialLinearGroup -- guard against import creep

open Matrix

variable {X α l m n p S R : Type*} {m' n' : l → Type*}

-- INSTANCE (free from Core): [TopologicalSpace

-- INSTANCE (free from Core): [TopologicalSpace

-- INSTANCE (free from Core): [TopologicalSpace

section Set

theorem IsOpen.matrix [Finite m] [Finite n]
    [TopologicalSpace R] {S : Set R} (hS : IsOpen S) :
    IsOpen (S.matrix : Set (Matrix m n R)) :=
  Set.matrix_eq_pi ▸
    (isOpen_set_pi Set.finite_univ fun _ _ =>
    isOpen_set_pi Set.finite_univ fun _ _ => hS).preimage continuous_id

theorem IsCompact.matrix [TopologicalSpace R] {S : Set R} (hS : IsCompact S) :
    IsCompact (S.matrix : Set (Matrix m n R)) :=
  isCompact_pi_infinite fun _ => isCompact_pi_infinite fun _ => hS

end Set

/-! ### Lemmas about continuity of operations -/

section Continuity

variable [TopologicalSpace X] [TopologicalSpace R]

-- INSTANCE (free from Core): [SMul

-- INSTANCE (free from Core): [TopologicalSpace

-- INSTANCE (free from Core): [Add

-- INSTANCE (free from Core): [Neg

-- INSTANCE (free from Core): [AddGroup
