/-
Extracted from Dynamics/PeriodicPts/Defs.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Periodic points

A point `x : α` is a periodic point of `f : α → α` of period `n` if `f^[n] x = x`.

## Main definitions

* `IsPeriodicPt f n x` : `x` is a periodic point of `f` of period `n`, i.e. `f^[n] x = x`.
  We do not require `n > 0` in the definition.
* `ptsOfPeriod f n` : the set `{x | IsPeriodicPt f n x}`. Note that `n` is not required to
  be the minimal period of `x`.
* `periodicPts f` : the set of all periodic points of `f`.
* `minimalPeriod f x` : the minimal period of a point `x` under an endomorphism `f` or zero
  if `x` is not a periodic point of `f`.
* `orbit f x`: the cycle `[x, f x, f (f x), ...]` for a periodic point.
* `MulAction.period g x` : the minimal period of a point `x` under the multiplicative action of `g`;
  an equivalent `AddAction.period g x` is defined for additive actions.

## Main statements

We provide “dot syntax”-style operations on terms of the form `h : IsPeriodicPt f n x` including
arithmetic operations on `n` and `h.map (hg : SemiconjBy g f f')`. We also prove that `f`
is bijective on each set `ptsOfPeriod f n` and on `periodicPts f`. Finally, we prove that `x`
is a periodic point of `f` of period `n` if and only if `minimalPeriod f x | n`.

## References

* https://en.wikipedia.org/wiki/Periodic_point

-/

assert_not_exists MonoidWithZero

open Set

namespace Function

open Function (Commute)

variable {α : Type*} {β : Type*} {f fa : α → α} {fb : β → β} {x y : α} {m n : ℕ}

def IsPeriodicPt (f : α → α) (n : ℕ) (x : α) :=
  IsFixedPt f^[n] x

theorem IsFixedPt.isPeriodicPt (hf : IsFixedPt f x) (n : ℕ) : IsPeriodicPt f n x :=
  hf.iterate n

theorem is_periodic_id (n : ℕ) (x : α) : IsPeriodicPt id n x :=
  (isFixedPt_id x).isPeriodicPt n

theorem isPeriodicPt_zero (f : α → α) (x : α) : IsPeriodicPt f 0 x :=
  isFixedPt_id x

namespace IsPeriodicPt
