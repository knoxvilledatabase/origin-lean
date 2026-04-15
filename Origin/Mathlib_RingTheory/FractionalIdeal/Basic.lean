/-
Extracted from RingTheory/FractionalIdeal/Basic.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Fractional ideals

This file defines fractional ideals of an integral domain and proves basic facts about them.

## Main definitions
Let `S` be a submonoid of an integral domain `R` and `P` the localization of `R` at `S`.
* `IsFractional` defines which `R`-submodules of `P` are fractional ideals
* `FractionalIdeal S P` is the type of fractional ideals in `P`
* a coercion `coeIdeal : Ideal R → FractionalIdeal S P`
* `CommSemiring (FractionalIdeal S P)` instance:
  the typical ideal operations generalized to fractional ideals
* `Lattice (FractionalIdeal S P)` instance

## Main statements

  * the `MulLeftMono` and `MulRightMono` instances state that ideal multiplication is monotone
  * `mul_div_self_cancel_iff` states that `1 / I` is the inverse of `I` if one exists

## Implementation notes

Fractional ideals are considered equal when they contain the same elements,
independent of the denominator `a : R` such that `a I ⊆ R`.
Thus, we define `FractionalIdeal` to be the subtype of the predicate `IsFractional`,
instead of having `FractionalIdeal` be a structure of which `a` is a field.

Most definitions in this file specialize operations from submodules to fractional ideals,
proving that the result of this operation is fractional if the input is fractional.
Exceptions to this rule are defining `(+) := (⊔)` and `⊥ := 0`,
in order to reuse their respective proof terms.
We can still use `simp` to show `↑I + ↑J = ↑(I + J)` and `↑⊥ = ↑0`.

Many results in fact do not need that `P` is a localization, only that `P` is an
`R`-algebra. We omit the `IsLocalization` parameter whenever this is practical.
Similarly, we don't assume that the localization is a field until we need it to
define ideal quotients. When this assumption is needed, we replace `S` with `R⁰`,
making the localization a field.

## References

  * https://en.wikipedia.org/wiki/Fractional_ideal

## Tags

fractional ideal, fractional ideals, invertible ideal
-/

open IsLocalization Pointwise nonZeroDivisors

section Defs

variable {R : Type*} [CommRing R] {S : Submonoid R} {P : Type*} [CommRing P]

variable [Algebra R P]

variable (S)

def IsFractional (I : Submodule R P) :=
  ∃ a ∈ S, ∀ b ∈ I, IsInteger R (a • b)

variable (P)

def FractionalIdeal :=
  { I : Submodule R P // IsFractional S I }

end Defs

namespace FractionalIdeal

open Set Submodule

variable {R : Type*} [CommRing R] {S : Submonoid R} {P : Type*} [CommRing P]

variable [Algebra R P]
