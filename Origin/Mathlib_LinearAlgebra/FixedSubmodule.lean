/-
Extracted from LinearAlgebra/FixedSubmodule.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The fixed submodule of a linear map

- `LinearMap.fixedSubmodule`: the submodule of a linear map consisting of its fixed points.

-/

namespace LinearMap

open Pointwise Submodule MulAction

variable {R : Type*} [Semiring R]
  {U V : Type*} [AddCommMonoid U] [AddCommMonoid V]
  [Module R U] [Module R V] (e : V ≃ₗ[R] V)

def fixedSubmodule (f : V →ₗ[R] V) : Submodule R V where
  carrier := { x | f x = x }
  add_mem' {x y} hx hy := by aesop
  zero_mem' := by simp
  smul_mem' r x hx := by aesop
