/-
Extracted from LinearAlgebra/LinearIndependent/Defs.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

public meta import Mathlib.Lean.Expr.ExtraRecognizers

/-!

# Linear independence

This file defines linear independence in a module or vector space.

It is inspired by Isabelle/HOL's linear algebra, and hence indirectly by HOL Light.

We define `LinearIndependent R v` as `Function.Injective (Finsupp.linearCombination R v)`. Here
`Finsupp.linearCombination` is the linear map sending a function `f : ι →₀ R` with finite support to
the linear combination of vectors from `v` with these coefficients.

The goal of this file is to define linear independence and to prove that several other
statements are equivalent to this one, including `ker (Finsupp.linearCombination R v) = ⊥` and
some versions with explicitly written linear combinations.

## Main definitions
All definitions are given for families of vectors, i.e. `v : ι → M` where `M` is the module or
vector space and `ι : Type*` is an arbitrary indexing type.

* `LinearIndependent R v` states that the elements of the family `v` are linearly independent.

* `LinearIndepOn R v s` states that the elements of the family `v` indexed by the members
  of the set `s : Set ι` are linearly independent.

* `LinearIndependent.repr hv x` returns the linear combination representing `x : span R (range v)`
  on the linearly independent vectors `v`, given `hv : LinearIndependent R v`
  (using classical choice). `LinearIndependent.repr hv` is provided as a linear map.

* `LinearIndependent.Maximal` states that there exists no linear independent family that strictly
  includes the given one.

## Main results

* `Fintype.linearIndependent_iff`: if `ι` is a finite type, then any function `f : ι → R` has
  finite support, so we can reformulate the statement using `∑ i : ι, f i • v i` instead of a sum
  over an auxiliary `s : Finset ι`;

## Implementation notes

We use families instead of sets in `LinearIndependent` because it allows us to say that two
identical vectors are linearly dependent.

If you want to use sets, use `LinearIndepOn id s` given a set `s : Set M`. The lemmas
`LinearIndependent.linearIndepOn_id` and `LinearIndependent.of_linearIndepOn_id_range` connect those
two worlds.

In this file we prove some variants of results on different kinds of (semi)rings. We distinguish
them by using suffixes in their names, e.g. `linearIndependent_iffₛ` for semirings,
`linearIndependent_iffₒₛ` for (canonically) ordered semirings, and `linearIndependent_iff` (without
suffix) for rings.

## TODO

This file contains much more than definitions.

Rework proofs to hold in semirings, by avoiding the path through
`ker (Finsupp.linearCombination R v) = ⊥`.

## Tags

linearly dependent, linear dependence, linearly independent, linear independence

-/

assert_not_exists Cardinal

noncomputable section

open Function Module Set Submodule

universe u' u

variable {ι : Type u'} {ι' : Type*} {R : Type*} {K : Type*} {s : Set ι}

variable {M : Type*} {M' : Type*} {V : Type u}

section Semiring

variable {v : ι → M}

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M']

variable [Module R M] [Module R M']

variable (R) (v)

def LinearIndependent : Prop :=
  Injective (Finsupp.linearCombination R v)

open Lean PrettyPrinter.Delaborator SubExpr in
