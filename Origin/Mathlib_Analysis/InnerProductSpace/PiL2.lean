/-
Extracted from Analysis/InnerProductSpace/PiL2.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# `L²` inner product space structure on finite products of inner product spaces

The `L²` norm on a finite product of inner product spaces is compatible with an inner product
$$
\langle x, y\rangle = \sum \langle x_i, y_i \rangle.
$$
This is recorded in this file as an inner product space instance on `PiLp 2`.

This file develops the notion of a finite-dimensional Hilbert space over `𝕜 = ℂ, ℝ`, referred to as
`E`. We define an `OrthonormalBasis 𝕜 ι E` as a linear isometric equivalence
between `E` and `EuclideanSpace 𝕜 ι`. Then `stdOrthonormalBasis` shows that such an equivalence
always exists if `E` is finite dimensional. We provide language for converting between a basis
that is orthonormal and an orthonormal basis (e.g. `Basis.toOrthonormalBasis`). We show that
orthonormal bases for each summand in a direct sum of spaces can be combined into an orthonormal
basis for the whole sum in `DirectSum.IsInternal.subordinateOrthonormalBasis`. In
the last section, various properties of matrices are explored.

## Main definitions

- `EuclideanSpace 𝕜 n`: defined to be `PiLp 2 (n → 𝕜)` for any `Fintype n`, i.e., the space
  from functions to `n` to `𝕜` with the `L²` norm. We register several instances on it (notably
  that it is a finite-dimensional inner product space), and provide a `!ₚ[]` notation (for numeric
  subscripts like `₂`) for the case when the indexing type is `Fin n`.

- `OrthonormalBasis 𝕜 ι`: defined to be an isometry to Euclidean space from a given
  finite-dimensional inner product space, `E ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 ι`.

- `Basis.toOrthonormalBasis`: constructs an `OrthonormalBasis` for a finite-dimensional
  Euclidean space from a `Basis` which is `Orthonormal`.

- `Orthonormal.exists_orthonormalBasis_extension`: provides an existential result of an
  `OrthonormalBasis` extending a given orthonormal set

- `exists_orthonormalBasis`: provides an orthonormal basis on a finite-dimensional vector space

- `stdOrthonormalBasis`: provides an arbitrarily-chosen `OrthonormalBasis` of a given
  finite-dimensional inner product space

For consequences in infinite dimension (Hilbert bases, etc.), see the file
`Analysis.InnerProductSpace.L2Space`.

-/

open Module Real Set Filter RCLike Submodule Function Uniformity Topology NNReal ENNReal

  ComplexConjugate DirectSum WithLp

noncomputable section

variable {ι ι' 𝕜 : Type*} [RCLike 𝕜]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

variable {F' : Type*} [NormedAddCommGroup F'] [InnerProductSpace ℝ F']

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

-- INSTANCE (free from Core): PiLp.innerProductSpace

abbrev EuclideanSpace (𝕜 : Type*) (n : Type*) : Type _ :=
  PiLp 2 fun _ : n => 𝕜

section Notation

open Lean Meta Elab Term Macro TSyntax PrettyPrinter.Delaborator SubExpr

open Mathlib.Tactic (subscriptTerm)

syntax (name := PiLp.vecNotation) "!" noWs subscriptTerm noWs "[" term,* "]" : term

macro_rules | `(!$p:subscript[$e:term,*]) => do

  let n := e.getElems.size

  `(WithLp.toLp $p (V := ∀ _ : Fin $(quote n), _) ![$e,*])
