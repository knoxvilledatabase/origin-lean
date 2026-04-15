/-
Extracted from FieldTheory/Minpoly/IsConjRoot.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Conjugate roots

Given two elements `x` and `y` of some `K`-algebra, these two elements are *conjugate roots*
over `K` if they have the same minimal polynomial over `K`.

## Main definitions

* `IsConjRoot`: `IsConjRoot K x y` means `y` is a conjugate root of `x` over `K`.

## Main results

* `isConjRoot_iff_exists_algEquiv`: Let `L / K` be a normal field extension. For any two elements
  `x` and `y` in `L`, `IsConjRoot K x y` is equivalent to the existence of an algebra equivalence
  `σ : Gal(L/K)` such that `y = σ x`.
* `notMem_iff_exists_ne_and_isConjRoot`: Let `L / K` be a field extension. If `x` is a separable
  element over `K` and the minimal polynomial of `x` splits in `L`, then `x` is not in the `K` iff
  there exists a different conjugate root of `x` in `L` over `K`.

## TODO
* Move `IsConjRoot` to earlier files and refactor the theorems in field theory using `IsConjRoot`.

* Prove `IsConjRoot.smul`, if `x` and `y` are conjugate roots, then so are `r • x` and `r • y`.

## Tags
conjugate root, minimal polynomial
-/

open Polynomial minpoly Module IntermediateField

variable {R K L S A B : Type*} [CommRing R] [CommRing S] [Ring A] [Ring B] [Field K] [Field L]

variable [Algebra R S] [Algebra R A] [Algebra R B]

variable [Algebra K S] [Algebra K L] [Algebra K A] [Algebra L S]

variable (R) in

def IsConjRoot (x y : A) : Prop := minpoly R x = minpoly R y

namespace IsConjRoot
