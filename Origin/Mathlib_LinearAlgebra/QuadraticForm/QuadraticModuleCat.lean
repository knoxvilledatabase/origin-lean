/-
Extracted from LinearAlgebra/QuadraticForm/QuadraticModuleCat.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# The category of quadratic modules
-/

open CategoryTheory

universe v u

variable (R : Type u) [CommRing R]

structure QuadraticModuleCat extends ModuleCat.{v} R where
  /-- The quadratic form associated with the module. -/
  form : QuadraticForm R carrier

variable {R}

namespace QuadraticModuleCat

open QuadraticForm QuadraticMap

-- INSTANCE (free from Core): :
