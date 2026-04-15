/-
Extracted from LinearAlgebra/CliffordAlgebra/CategoryTheory.lean
Genuine: 1 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.QuadraticForm.QuadraticModuleCat
import Mathlib.Algebra.Category.AlgebraCat.Basic

/-! # Category-theoretic interpretations of `CliffordAlgebra`

## Main definitions

* `QuadraticModuleCat.cliffordAlgebra`: the functor from quadratic modules to algebras
-/

universe v u

open CategoryTheory

variable {R : Type u} [CommRing R]

@[simps]
def QuadraticModuleCat.cliffordAlgebra : QuadraticModuleCat.{u} R ⥤ AlgebraCat.{u} R where
  obj M := AlgebraCat.of R (CliffordAlgebra M.form)
  map {_M _N} f := AlgebraCat.ofHom <| CliffordAlgebra.map f.toIsometry
  map_id _M := by simp
  map_comp {_M _N _P} f g := by ext; simp
