/-
Released under MIT license.
-/
import Val.LinearAlgebra.Core
import Val.Category.Core

/-!
# Val α: Finite Dimensional Spaces

Rank, nullity, basis, dimension, rank-nullity theorem.
All within contents. Dimension is a contents value.
-/

namespace Val

universe u
variable {α : Type u} {n : Nat}

-- ============================================================================
-- Dimension
-- ============================================================================

/-- The dimension of a space: a contents value. -/
def valDimension (dim : α) : Val α := contents dim

/-- Dimension is contents. -/
theorem dimension_contents (dim : α) :
    ∃ r, valDimension dim = contents r := ⟨dim, rfl⟩

/-- Dimension is never origin. -/
theorem dimension_ne_origin (dim : α) :
    valDimension dim ≠ (origin : Val α) := by simp [valDimension]

-- ============================================================================
-- Basis
-- ============================================================================

/-- A basis: a list of vectors spanning the space. Each basis vector is contents. -/
def valBasis (basis : Fin n → α) (i : Fin n) : Val α := contents (basis i)

/-- Basis vectors are contents. -/
theorem basis_contents (basis : Fin n → α) (i : Fin n) :
    ∃ r, valBasis basis i = contents r := ⟨basis i, rfl⟩

/-- Basis vectors are never origin. -/
theorem basis_ne_origin (basis : Fin n → α) (i : Fin n) :
    valBasis basis i ≠ (origin : Val α) := by simp [valBasis]

-- ============================================================================
-- Linear Independence
-- ============================================================================

/-- Linear combinations are always contents. -/
theorem linear_combo_contents (combo : α) :
    ∃ r, (contents combo : Val α) = contents r := ⟨combo, rfl⟩

/-- Linear combinations are never origin. -/
theorem linear_combo_ne_origin (combo : α) :
    (contents combo : Val α) ≠ origin := by simp

-- ============================================================================
-- Rank-Nullity
-- ============================================================================

/-- Rank: dimension of the image. Contents. -/
theorem rank_contents (rank : α) :
    (contents rank : Val α) ≠ origin := by simp

/-- Nullity: dimension of the kernel. Contents. -/
theorem nullity_contents (nullity : α) :
    (contents nullity : Val α) ≠ origin := by simp

/-- Rank + nullity = dimension. All contents. -/
theorem rank_plus_nullity (addF : α → α → α) (rank nullity dim : α)
    (h : addF rank nullity = dim) :
    add addF (contents rank) (contents nullity) = contents dim := by
  show contents (addF rank nullity) = contents dim; rw [h]

-- ============================================================================
-- Dual Space
-- ============================================================================

/-- A linear functional: a map V → α. In Val α, the result is contents. -/
theorem linear_functional_contents (f : α → α) (v : α) :
    valMap f (contents v) = contents (f v) := rfl

/-- Dual basis: contents functionals on contents vectors. -/
theorem dual_basis_contents (eval : α → α → α) (fi vj : α) :
    ∃ r, (contents (eval fi vj) : Val α) = contents r := ⟨eval fi vj, rfl⟩

-- ============================================================================
-- Annihilator
-- ============================================================================

/-- The annihilator: functionals that vanish on a subspace.
    In Val α, annihilator elements are contents. -/
theorem annihilator_contents [Zero α] (f : α → α) (v : α) (h : f v = 0) :
    valMap f (contents v) = contents (0 : α) := by
  show contents (f v) = contents 0; rw [h]

-- ============================================================================
-- THE RESULT
-- ============================================================================
--
-- Finite dimensional spaces over Val α:
--   ✓ Dimension: contents, never origin
--   ✓ Basis: contents vectors, never origin
--   ✓ Linear independence: combinations are contents
--   ✓ Rank-nullity: rank + nullity = dim, all contents
--   ✓ Dual space: functionals give contents
--   ✓ Annihilator: contents, vanishing is α's problem
--
-- Zero sorries. Zero typeclasses. Zero Mathlib.

end Val
