/-
Extracted from RingTheory/GradedAlgebra/HomogeneousLocalization.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Homogeneous Localization

## Notation
- `ι` is a commutative monoid;
- `A` is a commutative ring;
- `σ` is a class of additive subgroups of `A`;
- `𝒜 : ι → σ` is the grading of `A`;
- `x : Submonoid A` is a submonoid

## Main definitions and results

This file constructs the subring of `Aₓ` where the numerator and denominator have the same grading,
i.e. `{a/b ∈ Aₓ | ∃ (i : ι), a ∈ 𝒜ᵢ ∧ b ∈ 𝒜ᵢ}`.

* `HomogeneousLocalization.NumDenSameDeg`: a structure with a numerator and denominator field
  where they are required to have the same grading.

However `NumDenSameDeg 𝒜 x` cannot have a ring structure for many reasons, for example if `c`
is a `NumDenSameDeg`, then generally, `c + (-c)` is not necessarily `0` for degree reasons ---
`0` is considered to have grade zero (see `deg_zero`) but `c + (-c)` has the same degree as `c`. To
circumvent this, we quotient `NumDenSameDeg 𝒜 x` by the kernel of `c ↦ c.num / c.den`.

* `HomogeneousLocalization.NumDenSameDeg.embedding`: for `x : Submonoid A` and any
  `c : NumDenSameDeg 𝒜 x`, or equivalent a numerator and a denominator of the same degree,
  we get an element `c.num / c.den` of `Aₓ`.
* `HomogeneousLocalization`: `NumDenSameDeg 𝒜 x` quotiented by kernel of `embedding 𝒜 x`.
* `HomogeneousLocalization.val`: if `f : HomogeneousLocalization 𝒜 x`, then `f.val` is an element
  of `Aₓ`. In another word, one can view `HomogeneousLocalization 𝒜 x` as a subring of `Aₓ`
  through `HomogeneousLocalization.val`.
* `HomogeneousLocalization.num`: if `f : HomogeneousLocalization 𝒜 x`, then `f.num : A` is the
  numerator of `f`.
* `HomogeneousLocalization.den`: if `f : HomogeneousLocalization 𝒜 x`, then `f.den : A` is the
  denominator of `f`.
* `HomogeneousLocalization.deg`: if `f : HomogeneousLocalization 𝒜 x`, then `f.deg : ι` is the
  degree of `f` such that `f.num ∈ 𝒜 f.deg` and `f.den ∈ 𝒜 f.deg`
  (see `HomogeneousLocalization.num_mem_deg` and `HomogeneousLocalization.den_mem_deg`).
* `HomogeneousLocalization.num_mem_deg`: if `f : HomogeneousLocalization 𝒜 x`, then
  `f.num_mem_deg` is a proof that `f.num ∈ 𝒜 f.deg`.
* `HomogeneousLocalization.den_mem_deg`: if `f : HomogeneousLocalization 𝒜 x`, then
  `f.den_mem_deg` is a proof that `f.den ∈ 𝒜 f.deg`.
* `HomogeneousLocalization.eq_num_div_den`: if `f : HomogeneousLocalization 𝒜 x`, then
  `f.val : Aₓ` is equal to `f.num / f.den`.

* `HomogeneousLocalization.isLocalRing`: `HomogeneousLocalization 𝒜 x` is a local ring when `x` is
  the complement of some prime ideals.

* `HomogeneousLocalization.map`: Let `A` and `B` be two graded rings and `g : A → B` a
  grading-preserving ring map. If `P ≤ A` and `Q ≤ B` are submonoids such that `P ≤ g⁻¹(Q)`, then
  `g` induces a ring map between the homogeneous localization of `A` at `P` and the homogeneous
  localization of `B` at `Q`.

## References

* [Robin Hartshorne, *Algebraic Geometry*][Har77]


-/

noncomputable section

open DirectSum Pointwise

open DirectSum SetLike

variable {ι A σ : Type*}

variable [CommRing A] [SetLike σ A]

local notation "at " x => Localization x

namespace HomogeneousLocalization

structure NumDenSameDeg (𝒜 : ι → σ) (x : Submonoid A) where
  deg : ι
  (num den : 𝒜 deg)
  den_mem : (den : A) ∈ x

end

namespace NumDenSameDeg

open SetLike.GradedMonoid Submodule
