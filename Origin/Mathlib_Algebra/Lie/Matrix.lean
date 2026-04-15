/-
Extracted from Algebra/Lie/Matrix.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Lie algebras of matrices

An important class of Lie algebras are those arising from the associative algebra structure on
square matrices over a commutative ring. This file provides some very basic definitions whose
primary value stems from their utility when constructing the classical Lie algebras using matrices.

## Main definitions

  * `lieEquivMatrix'`
  * `Matrix.lieConj`
  * `Matrix.reindexLieEquiv`

## Tags

lie algebra, matrix
-/

universe u v w w₁ w₂

section Matrices

open scoped Matrix

variable {R : Type u} [CommRing R]

variable {n : Type w} [DecidableEq n] [Fintype n]

def lieEquivMatrix' : Module.End R (n → R) ≃ₗ⁅R⁆ Matrix n n R :=
  { LinearMap.toMatrix' with
    map_lie' := fun {T S} => by
      let f := @LinearMap.toMatrix' R _ n n _ _
      change f (T.comp S - S.comp T) = f T * f S - f S * f T
      have h : ∀ T S : Module.End R _, f (T.comp S) = f T * f S := LinearMap.toMatrix'_comp
      rw [map_sub, h, h] }
