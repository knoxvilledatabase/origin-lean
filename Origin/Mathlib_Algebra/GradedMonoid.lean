/-
Extracted from Algebra/GradedMonoid.lean
Genuine: 2 of 4 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Additively-graded multiplicative structures

This module provides a set of heterogeneous typeclasses for defining a multiplicative structure
over the sigma type `GradedMonoid A` such that `(*) : A i → A j → A (i + j)`; that is to say, `A`
forms an additively-graded monoid. The typeclasses are:

* `GradedMonoid.GOne A`
* `GradedMonoid.GMul A`
* `GradedMonoid.GMonoid A`
* `GradedMonoid.GCommMonoid A`

These respectively imbue:

* `One (GradedMonoid A)`
* `Mul (GradedMonoid A)`
* `Monoid (GradedMonoid A)`
* `CommMonoid (GradedMonoid A)`

the base type `A 0` with:

* `GradedMonoid.GradeZero.One`
* `GradedMonoid.GradeZero.Mul`
* `GradedMonoid.GradeZero.Monoid`
* `GradedMonoid.GradeZero.CommMonoid`

and the `i`th grade `A i` with `A 0`-actions (`•`) defined as left-multiplication:

* (nothing)
* `GradedMonoid.GradeZero.SMul (A 0)`
* `GradedMonoid.GradeZero.MulAction (A 0)`
* (nothing)

For now, these typeclasses are primarily used in the construction of `DirectSum.Ring` and the rest
of that file.

## Dependent graded products

This also introduces `List.dProd`, which takes the (possibly non-commutative) product of a list
of graded elements of type `A i`. This definition primarily exists to allow `GradedMonoid.mk`
and `DirectSum.of` to be pulled outside a product, such as in `GradedMonoid.mk_list_dProd` and
`DirectSum.of_list_dProd`.

## Internally graded monoids

In addition to the above typeclasses, in the most frequent case when `A` is an indexed collection of
`SetLike` subobjects (such as `AddSubmonoid`s, `AddSubgroup`s, or `Submodule`s), this file
provides the `Prop` typeclasses:

* `SetLike.GradedOne A` (which provides the obvious `GradedMonoid.GOne A` instance)
* `SetLike.GradedMul A` (which provides the obvious `GradedMonoid.GMul A` instance)
* `SetLike.GradedMonoid A` (which provides the obvious `GradedMonoid.GMonoid A` and
  `GradedMonoid.GCommMonoid A` instances)

which respectively provide the API lemmas

* `SetLike.one_mem_graded`
* `SetLike.mul_mem_graded`
* `SetLike.pow_mem_graded`, `SetLike.list_prod_map_mem_graded`

Strictly this last class is unnecessary as it has no fields not present in its parents, but it is
included for convenience. Note that there is no need for `SetLike.GradedRing` or similar, as all
the information it would contain is already supplied by `GradedMonoid` when `A` is a collection
of objects satisfying `AddSubmonoidClass` such as `Submodule`s. These constructions are explored
in `Algebra.DirectSum.Internal`.

This file also defines:

* `SetLike.IsHomogeneousElem A` (which says that `a` is homogeneous iff `a ∈ A i` for some `i : ι`)
* `SetLike.homogeneousSubmonoid A`, which is, as the name suggests, the submonoid consisting of
  all the homogeneous elements.

## Tags

graded monoid
-/

variable {ι : Type*}

def GradedMonoid (A : ι → Type*) :=
  Sigma A

namespace GradedMonoid

-- INSTANCE (free from Core): {A

def mk {A : ι → Type*} : ∀ i, A i → GradedMonoid A :=
  Sigma.mk

/-! ### Actions -/

section actions

variable {α β} {A : ι → Type*}

-- INSTANCE (free from Core): [∀
