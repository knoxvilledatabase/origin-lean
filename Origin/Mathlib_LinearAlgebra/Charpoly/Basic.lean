/-
Extracted from LinearAlgebra/Charpoly/Basic.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!

# Characteristic polynomial

We define the characteristic polynomial of `f : M →ₗ[R] M`, where `M` is a finite and
free `R`-module. The proof that `f.charpoly` is the characteristic polynomial of the matrix of `f`
in any basis is in `LinearAlgebra/Charpoly/ToMatrix`.

## Main definition

* `LinearMap.charpoly f` : the characteristic polynomial of `f : M →ₗ[R] M`.

-/

universe u v w

variable {R : Type u} {M : Type v} [CommRing R]

variable [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M] (f : M →ₗ[R] M)

open Matrix Polynomial

noncomputable section

open Module.Free Polynomial Matrix

namespace LinearMap

section Basic

def charpoly : R[X] :=
  (toMatrix (chooseBasis R M) (chooseBasis R M) f).charpoly

theorem eval_charpoly (t : R) :
    f.charpoly.eval t = (algebraMap _ _ t - f).det := by
  rw [charpoly, Matrix.eval_charpoly, ← LinearMap.det_toMatrix (chooseBasis R M), map_sub,
    scalar_apply, toMatrix_algebraMap, scalar_apply]
