/-
Extracted from Dynamics/Circle/RotationNumber/TranslationNumber.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Translation number of a monotone real map that commutes with `x ↦ x + 1`

Let `f : ℝ → ℝ` be a monotone map such that `f (x + 1) = f x + 1` for all `x`. Then the limit
$$
  \tau(f)=\lim_{n\to\infty}{f^n(x)-x}{n}
$$
exists and does not depend on `x`. This number is called the *translation number* of `f`.
Different authors use different notation for this number: `τ`, `ρ`, `rot`, etc

In this file we define a structure `CircleDeg1Lift` for bundled maps with these properties, define
translation number of `f : CircleDeg1Lift`, prove some estimates relating `f^n(x)-x` to `τ(f)`. In
case of a continuous map `f` we also prove that `f` admits a point `x` such that `f^n(x)=x+m` if and
only if `τ(f)=m/n`.

Maps of this type naturally appear as lifts of orientation-preserving circle homeomorphisms. More
precisely, let `f` be an orientation-preserving homeomorphism of the circle $S^1=ℝ/ℤ$, and
consider a real number `a` such that
`⟦a⟧ = f 0`, where `⟦⟧` means the natural projection `ℝ → ℝ/ℤ`. Then there exists a unique
continuous function `F : ℝ → ℝ` such that `F 0 = a` and `⟦F x⟧ = f ⟦x⟧` for all `x` (this fact is
not formalized yet). This function is strictly monotone, continuous, and satisfies
`F (x + 1) = F x + 1`. The number `⟦τ F⟧ : ℝ / ℤ` is called the *rotation number* of `f`.
It does not depend on the choice of `a`.

## Main definitions

* `CircleDeg1Lift`: a monotone map `f : ℝ → ℝ` such that `f (x + 1) = f x + 1` for all `x`;
  the type `CircleDeg1Lift` is equipped with `Lattice` and `Monoid` structures; the
  multiplication is given by composition: `(f * g) x = f (g x)`.
* `CircleDeg1Lift.translationNumber`: translation number of `f : CircleDeg1Lift`.

## Main statements

We prove the following properties of `CircleDeg1Lift.translationNumber`.

* `CircleDeg1Lift.translationNumber_eq_of_dist_bounded`: if the distance between `(f^n) 0`
  and `(g^n) 0` is bounded from above uniformly in `n : ℕ`, then `f` and `g` have equal
  translation numbers.

* `CircleDeg1Lift.translationNumber_eq_of_semiconjBy`: if two `CircleDeg1Lift` maps `f`, `g`
  are semiconjugate by a `CircleDeg1Lift` map, then `τ f = τ g`.

* `CircleDeg1Lift.translationNumber_units_inv`: if `f` is an invertible `CircleDeg1Lift` map
  (equivalently, `f` is a lift of an orientation-preserving circle homeomorphism), then
  the translation number of `f⁻¹` is the negative of the translation number of `f`.

* `CircleDeg1Lift.translationNumber_mul_of_commute`: if `f` and `g` commute, then
  `τ (f * g) = τ f + τ g`.

* `CircleDeg1Lift.translationNumber_eq_rat_iff`: the translation number of `f` is equal to
  a rational number `m / n` if and only if `(f^n) x = x + m` for some `x`.

* `CircleDeg1Lift.semiconj_of_bijective_of_translationNumber_eq`: if `f` and `g` are two
  bijective `CircleDeg1Lift` maps and their translation numbers are equal, then these
  maps are semiconjugate to each other.

* `CircleDeg1Lift.semiconj_of_group_action_of_forall_translationNumber_eq`: let `f₁` and `f₂` be
  two actions of a group `G` on the circle by degree 1 maps (formally, `f₁` and `f₂` are two
  homomorphisms from `G →* CircleDeg1Lift`). If the translation numbers of `f₁ g` and `f₂ g` are
  equal to each other for all `g : G`, then these two actions are semiconjugate by some
  `F : CircleDeg1Lift`. This is a version of Proposition 5.4 from [Étienne Ghys, Groupes
  d'homéomorphismes du cercle et cohomologie bornée][ghys87:groupes].

## Notation

We use a local notation `τ` for the translation number of `f : CircleDeg1Lift`.

## Implementation notes

We define the translation number of `f : CircleDeg1Lift` to be the limit of the sequence
`(f ^ (2 ^ n)) 0 / (2 ^ n)`, then prove that `((f ^ n) x - x) / n` tends to this number for any `x`.
This way it is much easier to prove that the limit exists and basic properties of the limit.

We define translation number for a wider class of maps `f : ℝ → ℝ` instead of lifts of orientation
preserving circle homeomorphisms for two reasons:

* non-strictly monotone circle self-maps with discontinuities naturally appear as Poincaré maps
  for some flows on the two-torus (e.g., one can take a constant flow and glue in a few Cherry
  cells);
* definition and some basic properties still work for this class.

## References

* [Étienne Ghys, Groupes d'homéomorphismes du cercle et cohomologie bornée][ghys87:groupes]

## TODO

Here are some short-term goals.

* Introduce a structure or a typeclass for lifts of circle homeomorphisms. We use
  `Units CircleDeg1Lift` for now, but it's better to have a dedicated type (or a typeclass?).

* Prove that the `SemiconjBy` relation on circle homeomorphisms is an equivalence relation.

* Introduce `ConditionallyCompleteLattice` structure, use it in the proof of
  `CircleDeg1Lift.semiconj_of_group_action_of_forall_translationNumber_eq`.

* Prove that the orbits of the irrational rotation are dense in the circle. Deduce that a
  homeomorphism with an irrational rotation is semiconjugate to the corresponding irrational
  translation by a continuous `CircleDeg1Lift`.

## Tags

circle homeomorphism, rotation number
-/

open Filter Set Int Topology

open Function hiding Commute

/-!
### Definition and monoid structure
-/

structure CircleDeg1Lift : Type extends ℝ →o ℝ where
  map_add_one' : ∀ x, toFun (x + 1) = toFun x + 1

namespace CircleDeg1Lift

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :
