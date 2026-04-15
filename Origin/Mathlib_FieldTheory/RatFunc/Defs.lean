/-
Extracted from FieldTheory/RatFunc/Defs.lean
Genuine: 12 | Conflates: 0 | Dissolved: 8 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.RingTheory.Localization.FractionRing

/-!
# The field of rational functions

Files in this folder define the field `RatFunc K` of rational functions over a field `K`, show it
is the field of fractions of `K[X]` and provide the main results concerning it. This file contains
the basic definition.

For connections with Laurent Series, see `Mathlib.RingTheory.LaurentSeries`.

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
All these maps get `simp`ed to bundled morphisms like `algebraMap K[X] (RatFunc K)`
and `IsLocalization.algEquiv`.

There are separate lifts and maps of homomorphisms, to provide routes of lifting even when
the codomain is not a field or even an integral domain.

## References

* [Kleiman, *Misconceptions about $K_X$*][kleiman1979]
* https://freedommathdance.blogspot.com/2012/11/misconceptions-about-kx.html
* https://stacks.math.columbia.edu/tag/01X1

-/

noncomputable section

open scoped Classical

open scoped nonZeroDivisors Polynomial

universe u v

variable (K : Type u)

structure RatFunc [CommRing K] : Type u where ofFractionRing ::

  toFractionRing : FractionRing K[X]

namespace RatFunc

section CommRing

variable {K}

variable [CommRing K]

section Rec

/-! ### Constructing `RatFunc`s and their induction principles -/

theorem ofFractionRing_injective : Function.Injective (ofFractionRing : _ → RatFunc K) :=
  fun _ _ => ofFractionRing.inj

theorem toFractionRing_injective : Function.Injective (toFractionRing : _ → FractionRing K[X])
  | ⟨x⟩, ⟨y⟩, xy => by subst xy; rfl

@[simp] lemma toFractionRing_eq_iff {x y : RatFunc K} :
    toFractionRing x = toFractionRing y ↔ x = y :=
  toFractionRing_injective.eq_iff

protected irreducible_def liftOn {P : Sort v} (x : RatFunc K) (f : K[X] → K[X] → P)
    (H : ∀ {p q p' q'} (_hq : q ∈ K[X]⁰) (_hq' : q' ∈ K[X]⁰), q' * p = q * p' → f p q = f p' q') :
    P :=
  Localization.liftOn (toFractionRing x) (fun p q => f p q) fun {_ _ q q'} h =>
    H q.2 q'.2 (let ⟨⟨_, _⟩, mul_eq⟩ := Localization.r_iff_exists.mp h
      mul_cancel_left_coe_nonZeroDivisors.mp mul_eq)

theorem liftOn_ofFractionRing_mk {P : Sort v} (n : K[X]) (d : K[X]⁰) (f : K[X] → K[X] → P)
    (H : ∀ {p q p' q'} (_hq : q ∈ K[X]⁰) (_hq' : q' ∈ K[X]⁰), q' * p = q * p' → f p q = f p' q') :
    RatFunc.liftOn (ofFractionRing (Localization.mk n d)) f @H = f n d := by
  rw [RatFunc.liftOn]
  exact Localization.liftOn_mk _ _ _ _

-- DISSOLVED: liftOn_condition_of_liftOn'_condition

section IsDomain

variable [IsDomain K]

protected irreducible_def mk (p q : K[X]) : RatFunc K :=
  ofFractionRing (algebraMap _ _ p / algebraMap _ _ q)

theorem mk_eq_div' (p q : K[X]) :
    RatFunc.mk p q = ofFractionRing (algebraMap _ _ p / algebraMap _ _ q) := by rw [RatFunc.mk]

theorem mk_zero (p : K[X]) : RatFunc.mk p 0 = ofFractionRing (0 : FractionRing K[X]) := by
  rw [mk_eq_div', RingHom.map_zero, div_zero]

theorem mk_coe_def (p : K[X]) (q : K[X]⁰) :
    RatFunc.mk p q = ofFractionRing (IsLocalization.mk' _ p q) := by
  simp only [mk_eq_div', ← Localization.mk_eq_mk', FractionRing.mk_eq_div]

theorem mk_def_of_mem (p : K[X]) {q} (hq : q ∈ K[X]⁰) :
    RatFunc.mk p q = ofFractionRing (IsLocalization.mk' (FractionRing K[X]) p ⟨q, hq⟩) := by
  simp only [← mk_coe_def]

-- DISSOLVED: mk_def_of_ne

-- DISSOLVED: mk_eq_localization_mk

theorem mk_one' (p : K[X]) :
    RatFunc.mk p 1 = ofFractionRing (algebraMap _ _ p) := by
  rw [← IsLocalization.mk'_one (M := K[X]⁰) (FractionRing K[X]) p, ← mk_coe_def, Submonoid.coe_one]

-- DISSOLVED: mk_eq_mk

-- DISSOLVED: liftOn_mk

-- DISSOLVED: liftOn'

-- DISSOLVED: liftOn'_mk

-- DISSOLVED: induction_on'

end IsDomain

end Rec

end CommRing

end RatFunc
