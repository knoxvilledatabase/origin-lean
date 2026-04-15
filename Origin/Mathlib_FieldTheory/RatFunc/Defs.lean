/-
Extracted from FieldTheory/RatFunc/Defs.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The field of rational functions

Files in this folder define the field `K⟮X⟯` of rational functions over a field `K`, show it
is the field of fractions of `K[X]` and provide the main results concerning it. This file contains
the basic definition.

For connections with Laurent Series, see `Mathlib/RingTheory/LaurentSeries.lean`.

## Main definitions
We provide a set of recursion and induction principles:
- `RatFunc.liftOn`: define a function by mapping a fraction of polynomials `p/q` to `f p q`,
  if `f` is well-defined in the sense that `p/q = p'/q' → f p q = f p' q'`.
- `RatFunc.liftOn'`: define a function by mapping a fraction of polynomials `p/q` to `f p q`,
  if `f` is well-defined in the sense that `f (a * p) (a * q) = f p' q'`.
- `RatFunc.induction_on`: if `P` holds on `p / q` for all polynomials `p q`, then `P` holds on all
  rational functions

## Implementation notes

To provide good API encapsulation and speed up unification problems,
`RatFunc` is defined as a structure, and all operations are `@[irreducible] def`s

We need a couple of maps to set up the `Field` and `IsFractionRing` structure,
namely `RatFunc.ofFractionRing`, `RatFunc.toFractionRing`, `RatFunc.mk` and
`RatFunc.toFractionRingRingEquiv`.
All these maps get `simp`ed to bundled morphisms like `algebraMap K[X] K⟮X⟯`
and `IsLocalization.algEquiv`.

There are separate lifts and maps of homomorphisms, to provide routes of lifting even when
the codomain is not a field or even an integral domain.

## References

* [Kleiman, *Misconceptions about $K_X$*][kleiman1979]
* https://freedommathdance.blogspot.com/2012/11/misconceptions-about-kx.html
* https://stacks.math.columbia.edu/tag/01X1

-/

noncomputable section

open scoped nonZeroDivisors Polynomial

universe u v

variable (K : Type u)

structure RatFunc [CommRing K] : Type u where ofFractionRing ::

  toFractionRing : FractionRing K[X]
