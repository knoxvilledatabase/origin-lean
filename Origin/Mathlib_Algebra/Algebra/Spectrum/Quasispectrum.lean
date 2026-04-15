/-
Extracted from Algebra/Algebra/Spectrum/Quasispectrum.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Quasiregularity and quasispectrum

For a non-unital ring `R`, an element `r : R` is *quasiregular* if it is invertible in the monoid
`(R, ∘)` where `x ∘ y := y + x + x * y` with identity `0 : R`. We implement this both as a type
synonym `PreQuasiregular` which has an associated `Monoid` instance (note: *not* an `AddMonoid`
instance despite the fact that `0 : R` is the identity in this monoid) so that one may access
the quasiregular elements of `R` as `(PreQuasiregular R)ˣ`, but also as a predicate
`IsQuasiregular`.

Quasiregularity is closely tied to invertibility. Indeed, `(PreQuasiregular A)ˣ` is isomorphic to
the subgroup of `Unitization R A` whose scalar part is `1`, whenever `A` is a non-unital
`R`-algebra, and moreover this isomorphism is implemented by the map
`(x : A) ↦ (1 + x : Unitization R A)`. It is because of this isomorphism, and the associated ties
with multiplicative invertibility, that we choose a `Monoid` (as opposed to an `AddMonoid`)
structure on `PreQuasiregular`.  In addition, in unital rings, we even have
`IsQuasiregular x ↔ IsUnit (1 + x)`.

The *quasispectrum* of `a : A` (with respect to `R`) is defined in terms of quasiregularity, and
this is the natural analogue of the `spectrum` for non-unital rings. Indeed, it is true that
`quasispectrum R a = spectrum R a ∪ {0}` when `A` is unital.

In Mathlib, the quasispectrum is the domain of the continuous functions associated to the
*non-unital* continuous functional calculus.

## Main definitions

+ `PreQuasiregular R`: a structure wrapping `R` that inherits a distinct `Monoid` instance when `R`
  is a non-unital semiring.
+ `Unitization.unitsFstOne`: the subgroup with carrier `{ x : (Unitization R A)ˣ | x.fst = 1 }`.
+ `unitsFstOne_mulEquiv_quasiregular`: the group isomorphism between
  `Unitization.unitsFstOne` and the units of `PreQuasiregular` (i.e., the quasiregular elements)
  which sends `(1, x) ↦ x`.
+ `IsQuasiregular x`: the proposition that `x : R` is a unit with respect to the monoid structure on
  `PreQuasiregular R`, i.e., there is some `u : (PreQuasiregular R)ˣ` such that `u.val` is
  identified with `x` (via the natural equivalence between `R` and `PreQuasiregular R`).
+ `quasispectrum R a`: in an algebra over the semifield `R`, this is the set
  `{r : R | (hr : IsUnit r) → ¬ IsQuasiregular (-(hr.unit⁻¹ • a))}`, which should be thought of
  as a version of the `spectrum` which is applicable in non-unital algebras.

## Main theorems

+ `isQuasiregular_iff_isUnit`: in a unital ring, `x` is quasiregular if and only if `1 + x` is
  a unit.
+ `quasispectrum_eq_spectrum_union_zero`: in a unital algebra `A` over a semifield `R`, the
  quasispectrum of `a : A` is the `spectrum` with zero added.
+ `Unitization.isQuasiregular_inr_iff`: `a : A` is quasiregular if and only if it is quasiregular
  in `Unitization R A` (via the coercion `Unitization.inr`).
+ `Unitization.quasispectrum_eq_spectrum_inr`: the quasispectrum of `a` in a non-unital `R`-algebra
  `A` is precisely the spectrum of `a` in `Unitization R A` (via the coercion `Unitization.inr`).
-/

structure PreQuasiregular (R : Type*) where
  /-- The value wrapped into a term of `PreQuasiregular`. -/
  val : R

namespace PreQuasiregular

variable {R : Type*} [NonUnitalSemiring R]
