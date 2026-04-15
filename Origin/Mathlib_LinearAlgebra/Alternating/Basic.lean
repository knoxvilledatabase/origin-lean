/-
Extracted from LinearAlgebra/Alternating/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Alternating Maps

We construct the bundled function `AlternatingMap`, which extends `MultilinearMap` with all the
arguments of the same type.

## Main definitions
* `AlternatingMap R M N ι` is the space of `R`-linear alternating maps from `ι → M` to `N`.
* `f.map_eq_zero_of_eq` expresses that `f` is zero when two inputs are equal.
* `f.map_swap` expresses that `f` is negated when two inputs are swapped.
* `f.map_perm` expresses how `f` varies by a sign change under a permutation of its inputs.
* An `AddCommMonoid`, `AddCommGroup`, and `Module` structure over `AlternatingMap`s that
  matches the definitions over `MultilinearMap`s.
* `MultilinearMap.domDomCongr`, for permuting the elements within a family.
* `MultilinearMap.alternatization`, which makes an alternating map out of a non-alternating one.
* `AlternatingMap.curryLeft`, for binding the leftmost argument of an alternating map indexed
  by `Fin n.succ`.

## Implementation notes
`AlternatingMap` is defined in terms of `map_eq_zero_of_eq`, as this is easier to work with than
using `map_swap` as a definition, and does not require `Neg N`.

`AlternatingMap`s are provided with a coercion to `MultilinearMap`, along with a set of
`norm_cast` lemmas that act on the algebraic structure:

* `AlternatingMap.coe_add`
* `AlternatingMap.coe_zero`
* `AlternatingMap.coe_sub`
* `AlternatingMap.coe_neg`
* `AlternatingMap.coe_smul`
-/

open Module

variable {R : Type*} [Semiring R]

variable {M : Type*} [AddCommMonoid M] [Module R M]

variable {N : Type*} [AddCommMonoid N] [Module R N]

variable {P : Type*} [AddCommMonoid P] [Module R P]

variable {M' : Type*} [AddCommGroup M'] [Module R M']

variable {N' : Type*} [AddCommGroup N'] [Module R N']

variable {ι ι' ι'' : Type*}

variable (R M N ι)

structure AlternatingMap extends MultilinearMap R (fun _ : ι => M) N where
  /-- The map is alternating: if `v` has two equal coordinates, then `f v = 0`. -/
  map_eq_zero_of_eq' : ∀ (v : ι → M) (i j : ι), v i = v j → i ≠ j → toFun v = 0
