/-
Extracted from LinearAlgebra/Matrix/Rank.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Rank of matrices

The rank of a matrix `A` is defined to be the rank of range of the linear map corresponding to `A`.
This definition does not depend on the choice of basis, see `Matrix.rank_eq_finrank_range_toLin`.

## Main declarations

* `Matrix.rank`: the rank of a matrix
* `Matrix.cRank`: the rank of a matrix as a cardinal
* `Matrix.eRank`: the rank of a matrix as a term in `ℕ∞`.

-/

open Matrix

namespace Matrix

open Module Cardinal Set Submodule

universe ul um um₀ un un₀ uo uR

variable {l : Type ul} {m : Type um} {m₀ : Type um₀} {n : Type un} {n₀ : Type un₀} {o : Type uo}

variable {R : Type uR}

section Infinite

variable [Semiring R]

noncomputable def cRank (A : Matrix m n R) : Cardinal := Module.rank R <| span R <| range Aᵀ
