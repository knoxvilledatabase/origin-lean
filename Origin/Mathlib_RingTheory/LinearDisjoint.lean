/-
Extracted from RingTheory/LinearDisjoint.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!

# Linearly disjoint subalgebras

This file contains basics about linearly disjoint subalgebras.
We adapt the definitions in <https://en.wikipedia.org/wiki/Linearly_disjoint>.
See the file `Mathlib/LinearAlgebra/LinearDisjoint.lean` for details.

## Main definitions

- `Subalgebra.LinearDisjoint`: two subalgebras are linearly disjoint, if they are
  linearly disjoint as submodules (`Submodule.LinearDisjoint`).

- `Subalgebra.LinearDisjoint.mulMap`: if two subalgebras `A` and `B` of `S / R` are
  linearly disjoint, then there is `A ⊗[R] B ≃ₐ[R] A ⊔ B` induced by multiplication in `S`.

## Main results

### Equivalent characterization of linear disjointness

- `Subalgebra.LinearDisjoint.linearIndependent_left_of_flat`:
  if `A` and `B` are linearly disjoint, and if `B` is a flat `R`-module, then for any family of
  `R`-linearly independent elements of `A`, they are also `B`-linearly independent.

- `Subalgebra.LinearDisjoint.of_basis_left_op`:
  conversely, if a basis of `A` is also `B`-linearly independent, then `A` and `B` are
  linearly disjoint.

- `Subalgebra.LinearDisjoint.linearIndependent_right_of_flat`:
  if `A` and `B` are linearly disjoint, and if `A` is a flat `R`-module, then for any family of
  `R`-linearly independent elements of `B`, they are also `A`-linearly independent.

- `Subalgebra.LinearDisjoint.of_basis_right`:
  conversely, if a basis of `B` is also `A`-linearly independent,
  then `A` and `B` are linearly disjoint.

- `Subalgebra.LinearDisjoint.linearIndependent_mul_of_flat`:
  if `A` and `B` are linearly disjoint, and if one of `A` and `B` is flat, then for any family of
  `R`-linearly independent elements `{ a_i }` of `A`, and any family of
  `R`-linearly independent elements `{ b_j }` of `B`, the family `{ a_i * b_j }` in `S` is
  also `R`-linearly independent.

- `Subalgebra.LinearDisjoint.of_basis_mul`:
  conversely, if `{ a_i }` is an `R`-basis of `A`, if `{ b_j }` is an `R`-basis of `B`,
  such that the family `{ a_i * b_j }` in `S` is `R`-linearly independent,
  then `A` and `B` are linearly disjoint.

### Equivalent characterization by `IsDomain` or `IsField` of tensor product

The following results are related to the equivalent characterizations in
<https://mathoverflow.net/questions/8324>.

- `Subalgebra.LinearDisjoint.isDomain_of_injective`,
  `Subalgebra.LinearDisjoint.exists_field_of_isDomain_of_injective`:
  under some flatness and injectivity conditions, if `A` and `B` are `R`-algebras, then `A ⊗[R] B`
  is a domain if and only if there exists an `R`-algebra which is a field that `A` and `B`
  embed into with linearly disjoint images.

- `Subalgebra.LinearDisjoint.of_isField`, `Subalgebra.LinearDisjoint.of_isField'`:
  if `A ⊗[R] B` is a field, then `A` and `B` are linearly disjoint, moreover, for any
  `R`-algebra `S` and injections of `A` and `B` into `S`, their images are linearly disjoint.

- `Algebra.TensorProduct.not_isField_of_transcendental`,
  `Algebra.TensorProduct.isAlgebraic_of_isField`:
  if `A` and `B` are flat `R`-algebras, both of them are transcendental, then `A ⊗[R] B` cannot
  be a field, equivalently, if `A ⊗[R] B` is a field, then one of them is algebraic.

### Other main results

- `Subalgebra.LinearDisjoint.symm_of_commute`, `Subalgebra.linearDisjoint_comm_of_commute`:
  linear disjointness is symmetric under some commutative conditions.

- `Subalgebra.LinearDisjoint.map`:
  linear disjointness is preserved by injective algebra homomorphisms.

- `Subalgebra.LinearDisjoint.bot_left`, `Subalgebra.LinearDisjoint.bot_right`:
  the image of `R` in `S` is linearly disjoint with any other subalgebras.

- `Subalgebra.LinearDisjoint.sup_free_of_free`: the compositum of two linearly disjoint
  subalgebras is a free module, if two subalgebras are also free modules.

- `Subalgebra.LinearDisjoint.rank_sup_of_free`,
  `Subalgebra.LinearDisjoint.finrank_sup_of_free`:
  if subalgebras `A` and `B` are linearly disjoint and they are
  free modules, then the rank of `A ⊔ B` is equal to the product of the rank of `A` and `B`.

- `Subalgebra.LinearDisjoint.of_finrank_sup_of_free`:
  conversely, if `A` and `B` are subalgebras which are free modules of finite rank,
  such that rank of `A ⊔ B` is equal to the product of the rank of `A` and `B`,
  then `A` and `B` are linearly disjoint.

- `Subalgebra.LinearDisjoint.adjoin_rank_eq_rank_left`:
  `Subalgebra.LinearDisjoint.adjoin_rank_eq_rank_right`:
  if `A` and `B` are linearly disjoint, if `A` is free and `B` is flat (resp. `B` is free and
  `A` is flat), then `[B[A] : B] = [A : R]` (resp. `[A[B] : A] = [B : R]`).
  See also `Subalgebra.adjoin_rank_le`.

- `Subalgebra.LinearDisjoint.of_finrank_coprime_of_free`:
  if the rank of `A` and `B` are coprime, and they satisfy some freeness condition,
  then `A` and `B` are linearly disjoint.

- `Subalgebra.LinearDisjoint.inf_eq_bot_of_commute`, `Subalgebra.LinearDisjoint.inf_eq_bot`:
  if `A` and `B` are linearly disjoint, under suitable technical conditions, they are disjoint.

The results with name containing "`of_commute`" also have corresponding specialized versions
assuming `S` is commutative.

## Tags

linearly disjoint, linearly independent, tensor product

-/

open Module

open scoped TensorProduct

noncomputable section

universe u v w

namespace Subalgebra

variable {R : Type u} {S : Type v}

section Semiring

variable [CommSemiring R] [Semiring S] [Algebra R S]

variable (A B : Subalgebra R S)

protected abbrev LinearDisjoint : Prop := (toSubmodule A).LinearDisjoint (toSubmodule B)

variable {A B}
