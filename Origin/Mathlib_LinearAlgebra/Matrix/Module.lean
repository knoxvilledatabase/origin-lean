/-
Extracted from LinearAlgebra/Matrix/Module.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Mₙ(R)-module structure on `Mⁿ`

## Main Results

- `Matrix.Module.matrixModule`: This instance shows `ι → M` is a module over `Matrix ι ι R`, and
  the action of it is a generalization of `Matrix.mulVec`, this is only available in the
  `Matrix.Module` namespace.
- `LinearMap.mapMatrixModule`: This defines a linear map from `ι → M` to `ι → N` over
  `Matrix ι ι R` induced by a linear map from `M` to `N` and together with `Matrix.matrixModule`
  it gives a functor from the category of `R`-modules to the category of `Matrix ι ι R`-modules.

## Tags
matrix, module
-/

variable {ι R M N P : Type*} [Ring R] [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]

namespace Matrix.Module

-- INSTANCE (free from Core): matrixModule

lemma smul_def' (N : Matrix ι ι R) (v : ι → M) : N • v = ∑ j : ι, fun i ↦ N i j • v j := by
  ext; simp [smul_def]
