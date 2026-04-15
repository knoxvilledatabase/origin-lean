/-
Extracted from Algebra/Tropical/Basic.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Tropical algebraic structures

This file defines algebraic structures of the (min-)tropical numbers, up to the tropical semiring.
Some basic lemmas about conversion from the base type `R` to `Tropical R` are provided, as
well as the expected implementations of tropical addition and tropical multiplication.

## Main declarations

* `Tropical R`: The type synonym of the tropical interpretation of `R`.
    If `[LinearOrder R]`, then addition on `R` is via `min`.
* `Semiring (Tropical R)`: A `LinearOrderedAddCommMonoidWithTop R`
    induces a `Semiring (Tropical R)`. If one solely has `[LinearOrderedAddCommMonoid R]`,
    then the "tropicalization of `R`" would be `Tropical (WithTop R)`.

## Implementation notes

The tropical structure relies on `Top` and `min`. For the max-tropical numbers, use
`OrderDual R`.

Inspiration was drawn from the implementation of `Additive`/`Multiplicative`/`Opposite`,
where a type synonym is created with some barebones API, and quickly made irreducible.

Algebraic structures are provided with as few typeclass assumptions as possible, even though
most references rely on `Semiring (Tropical R)` for building up the whole theory.

## References followed

* https://arxiv.org/pdf/math/0408099.pdf
* https://www.mathenjeans.fr/sites/default/files/sujets/tropical_geometry_-_casagrande.pdf

-/

assert_not_exists Nat.instMulOneClass

universe u v

variable (R : Type u)

def Tropical : Type u :=
  R

variable {R}

namespace Tropical

def trop : R → Tropical R :=
  id
