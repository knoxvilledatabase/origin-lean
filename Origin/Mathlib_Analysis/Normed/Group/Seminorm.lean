/-
Extracted from Analysis/Normed/Group/Seminorm.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Group seminorms

This file defines norms and seminorms in a group. A group seminorm is a function to the reals which
is positive-semidefinite and subadditive. A norm further only maps zero to zero.

## Main declarations

* `AddGroupSeminorm`: A function `f` from an additive group `G` to the reals that preserves zero,
  takes nonnegative values, is subadditive and such that `f (-x) = f x` for all `x`.
* `NonarchAddGroupSeminorm`: A function `f` from an additive group `G` to the reals that
  preserves zero, takes nonnegative values, is nonarchimedean and such that `f (-x) = f x`
  for all `x`.
* `GroupSeminorm`: A function `f` from a group `G` to the reals that sends one to zero, takes
  nonnegative values, is submultiplicative and such that `f x⁻¹ = f x` for all `x`.
* `AddGroupNorm`: A seminorm `f` such that `f x = 0 → x = 0` for all `x`.
* `NonarchAddGroupNorm`: A nonarchimedean seminorm `f` such that `f x = 0 → x = 0` for all `x`.
* `GroupNorm`: A seminorm `f` such that `f x = 0 → x = 1` for all `x`.

## Notes

The corresponding hom classes are defined in `Analysis.Order.Hom.Basic` to be used by absolute
values.

We do not define `NonarchAddGroupSeminorm` as an extension of `AddGroupSeminorm` to avoid
having a superfluous `add_le'` field in the resulting structure. The same applies to
`NonarchAddGroupNorm`.

## References

* [H. H. Schaefer, *Topological Vector Spaces*][schaefer1966]

## Tags

norm, seminorm
-/

assert_not_exists Finset

open Set

open NNReal

variable {R R' E F G : Type*}

structure AddGroupSeminorm (G : Type*) [AddGroup G] where
  -- Porting note: can't extend `ZeroHom G ℝ` because otherwise `to_additive` won't work since
  -- we aren't using old structures
  /-- The bare function of an `AddGroupSeminorm`. -/
  protected toFun : G → ℝ
  /-- The image of zero is zero. -/
  protected map_zero' : toFun 0 = 0
  /-- The seminorm is subadditive. -/
  protected add_le' : ∀ r s, toFun (r + s) ≤ toFun r + toFun s
  /-- The seminorm is invariant under negation. -/
  protected neg' : ∀ r, toFun (-r) = toFun r
