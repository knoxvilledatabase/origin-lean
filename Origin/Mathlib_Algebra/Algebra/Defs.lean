/-
Extracted from Algebra/Algebra/Defs.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Algebras over commutative semirings

In this file we define associative unital `Algebra`s over commutative (semi)rings.

* algebra homomorphisms `AlgHom` are defined in `Mathlib/Algebra/Algebra/Hom.lean`;

* algebra equivalences `AlgEquiv` are defined in `Mathlib/Algebra/Algebra/Equiv.lean`;

* `Subalgebra`s are defined in `Mathlib/Algebra/Algebra/Subalgebra/Basic.lean`;

* The category `AlgCat R` of `R`-algebras is defined in the file
  `Mathlib/Algebra/Category/AlgCat/Basic.lean`.

See the implementation notes for remarks about non-associative and non-unital algebras.

## Main definitions:

* `Algebra R A`: the algebra typeclass.
* `algebraMap R A : R →+* A`: the canonical map from `R` to `A`, as a `RingHom`. This is the
  preferred spelling of this map, it is also available as:
  * `Algebra.linearMap R A : R →ₗ[R] A`, a `LinearMap`.
  * `Algebra.ofId R A : R →ₐ[R] A`, an `AlgHom` (defined in a later file).

## Implementation notes

Given a commutative (semi)ring `R`, there are two ways to define an `R`-algebra structure on a
(possibly noncommutative) (semi)ring `A`:
* By endowing `A` with a morphism of rings `R →+* A` denoted `algebraMap R A` which lands in the
  center of `A`.
* By requiring `A` be an `R`-module such that the action associates and commutes with multiplication
  as `r • (a₁ * a₂) = (r • a₁) * a₂ = a₁ * (r • a₂)`.

We define `Algebra R A` in a way that subsumes both definitions, by extending `SMul R A` and
requiring that this scalar action `r • x` must agree with left multiplication by the image of the
structure morphism `algebraMap R A r * x`.

As a result, there are two ways to talk about an `R`-algebra `A` when `A` is a semiring:
1. ```lean
   variable [CommSemiring R] [Semiring A]
   variable [Algebra R A]
   ```
2. ```lean
   variable [CommSemiring R] [Semiring A]
   variable [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
   ```

The first approach implies the second via typeclass search; so any lemma stated with the second set
of arguments will automatically apply to the first set. Typeclass search does not know that the
second approach implies the first, but this can be shown with:
```lean
example {R A : Type*} [CommSemiring R] [Semiring A]
  [Module R A] [SMulCommClass R A A] [IsScalarTower R A A] : Algebra R A :=
Algebra.ofModule smul_mul_assoc mul_smul_comm
```

The advantage of the first approach is that `algebraMap R A` is available, and `AlgHom R A B` and
`Subalgebra R A` can be used. For concrete `R` and `A`, `algebraMap R A` is often definitionally
convenient.

The advantage of the second approach is that `CommSemiring R`, `Semiring A`, and `Module R A` can
all be relaxed independently; for instance, this allows us to:
* Replace `Semiring A` with `NonUnitalNonAssocSemiring A` in order to describe non-unital and/or
  non-associative algebras.
* Replace `CommSemiring R` and `Module R A` with `CommGroup R'` and `DistribMulAction R' A`,
  which when `R' = Rˣ` lets us talk about the "algebra-like" action of `Rˣ` on an
  `R`-algebra `A`.

While `AlgHom R A B` cannot be used in the second approach, `NonUnitalAlgHom R A B` still can.

You should always use the first approach when working with associative unital algebras, and mimic
the second approach only when you need to weaken a condition on either `R` or `A`.

-/

assert_not_exists Field Finset Module.End

universe u v w u₁ v₁

section Prio

class Algebra (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] extends SMul R A where
  /-- Embedding `R →+* A` given by `Algebra` structure.
  Use `algebraMap` from the root namespace instead. -/
  protected algebraMap : R →+* A
  commutes' : ∀ r x, algebraMap r * x = x * algebraMap r
  smul_def' : ∀ r x, r • x = algebraMap r * x

end Prio

def algebraMap (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] [Algebra R A] : R →+* A :=
  Algebra.algebraMap

theorem Algebra.subsingleton (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] [Algebra R A]
    [Subsingleton R] : Subsingleton A :=
  (algebraMap R A).codomain_trivial
