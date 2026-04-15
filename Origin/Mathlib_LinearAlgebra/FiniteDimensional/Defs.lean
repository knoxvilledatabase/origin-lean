/-
Extracted from LinearAlgebra/FiniteDimensional/Defs.lean
Genuine: 4 of 6 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Finite-dimensional vector spaces

This file defines finite-dimensional vector spaces and shows our definition is equivalent to
alternative definitions.

## Main definitions

Assume `V` is a vector space over a division ring `K`. There are (at least) three equivalent
definitions of finite-dimensionality of `V`:

- it admits a finite basis.
- it is finitely generated.
- it is Noetherian, i.e., every subspace is finitely generated.

We introduce a typeclass `FiniteDimensional K V` capturing this property. For ease of transfer of
proof, it is defined using the second point of view, i.e., as `Module.Finite`. However, we prove
that all these points of view are equivalent, with the following lemmas
(in the namespace `FiniteDimensional`):

- `Module.finBasis` and `Module.finBasisOfFinrankEq`
  are bases for finite-dimensional vector spaces, where the index type
  is `Fin` (in `Mathlib/LinearAlgebra/Dimension/Free.lean`)
- `fintypeBasisIndex` states that a finite-dimensional
  vector space has a finite basis
- `Module.Basis.finiteDimensional_of_finite` states that the existence of a basis indexed by a
  finite type implies finite-dimensionality
- `of_finite_basis` states that the existence of a basis indexed by a
  finite set implies finite-dimensionality
- `of_finrank_pos` states that a nonzero `finrank` (implying non-infinite dimension)
  implies finite-dimensionality
- `IsNoetherian.iff_fg` states that the space is finite-dimensional if and only if
  it is Noetherian (in `Mathlib/FieldTheory/Finiteness.lean`)

We make use of `finrank`, the dimension of a finite-dimensional space, returning a `Nat`, as
opposed to `Module.rank`, which returns a `Cardinal`. When the space has infinite dimension, its
`finrank` is by convention set to `0`. `finrank` is not defined using `FiniteDimensional`.
For basic results that do not need the `FiniteDimensional` class, import
`Mathlib/LinearAlgebra/Dimension/Finrank.lean`.

Preservation of finite-dimensionality and formulas for the dimension are given for
- submodules (`FiniteDimensional.finiteDimensional_submodule`)
- linear equivs, in `LinearEquiv.finiteDimensional`

## Implementation notes

You should not assume that there has been any effort to state lemmas as generally as possible.

Plenty of the results hold for general finitely generated modules (see
`Mathlib/RingTheory/Finiteness/Basic.lean`) or Noetherian modules (see
`Mathlib/RingTheory/Noetherian/Basic.lean`).
-/

assert_not_exists Module.Projective Subalgebra

universe u v v' w

open Cardinal Module Submodule

abbrev FiniteDimensional (K V : Type*) [DivisionRing K] [AddCommGroup V] [Module K V] :=
  Module.Finite K V

variable {K : Type u} {V : Type v}

namespace FiniteDimensional

variable [DivisionRing K] [AddCommGroup V] [Module K V] {V₂ : Type v'} [AddCommGroup V₂]
  [Module K V₂]

theorem of_injective (f : V →ₗ[K] V₂) (w : Function.Injective f) [FiniteDimensional K V₂] :
    FiniteDimensional K V :=
  Module.Finite.of_injective f w

theorem of_surjective (f : V →ₗ[K] V₂) (w : Function.Surjective f) [FiniteDimensional K V] :
    FiniteDimensional K V₂ :=
  Module.Finite.of_surjective f w

variable (K V)

-- INSTANCE (free from Core): finiteDimensional_pi

-- INSTANCE (free from Core): finiteDimensional_pi'

variable {K V}

theorem _root_.Module.Basis.finiteDimensional_of_finite {ι : Type w} [Finite ι] (h : Basis ι K V) :
    FiniteDimensional K V :=
  Module.Finite.of_basis h
