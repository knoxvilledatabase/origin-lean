/-
Extracted from Order/Interval/Finset/Gaps.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Gaps of disjoint closed intervals

This file defines `Finset.intervalGapsWithin` that computes the complement of the union of a
collection of pairwise disjoint subintervals of `[a, b]`.

If `LinearOrder α`, `F` is a finite subset of `α × α` such that for any `(x, y) ∈ F`,
`a ≤ x ≤ y ≤ b` and all such `[x, y]`'s are pairwise disjoint, `h` is a proof of `F.card = k`,
`i` is in `Fin (k + 1)`, we order `F` from left to right as
`(x 0, y 0), ..., (x (k - 1), y (k - 1))`, then `F.intervalGapsWithin h a b i` is
- `(a, b)` if `0 = i = k`;
- `(a, x 0)` if `0 = i < k`;
- `(y (i - 1), x i)` if `0 < i < k`;
- `(y (i - 1), b)` if `0 < i = k`.

Technically, the definition `F.intervalGapsWithin a b` does not require `F` to be pairwise disjoint
or endpoints to be within `[a, b]` or even require that `a ≤ b`, but it makes the most sense if
they are actually satisfied. If they are actually satisfied, then we show that
* `Finset.intervalGapsWithin_mapsTo`, `Finset.intervalGapsWithin_injective`,
  `Finset.intervalGapsWithin_surjOn`:
  `(fun j ↦ ((F.intervalGapsWithin h a b j.castSucc).2, (F.intervalGapsWithin h a b j.succ).1))` is
  a bijection between `Set.Iio k` and `F`.
* `Finset.intervalGapsWithin_le_fst`, `Finset.intervalGapsWithin_snd_le`,
  `Finset.intervalGapsWithin_fst_le_snd`:
  `[(F.intervalGapsWithin h a b j).1, (F.intervalGapsWithin h a b j).2]` is indeed a subinterval of
  `[a, b]` when `j < k`.
* `Finset.intervalGapsWithin_pairwiseDisjoint_Ioc`: the half-closed intervals
  `[(F.intervalGapsWithin h a b j).1, (F.intervalGapsWithin h a b j).2)` are pairwise disjoint
  for `j < k + 1`.
-/

open Fin Fin.NatCast Set

section IntervalGapsWithin

namespace Finset

variable {α : Type*} [LinearOrder α] (F : Finset (α × α)) {k : ℕ} (h : F.card = k) (a b : α)
  (j : ℕ)

noncomputable def intervalGapsWithin (i : Fin (k + 1)) : α × α := (fst, snd) where
  /-- The first coordinate of `F.intervalGapsWithin h a b i` is `a` if `i = 0`,
  `y (i - 1)` otherwise. -/
  fst := if hi : i = 0 then a else
    F.orderEmbOfFin (α := α ×ₗ α) h (i.pred hi) |>.2
  /-- The second coordinate of `F.intervalGapsWithin h a b i` is `b` if `i = k`,
  `x i` otherwise. -/
  snd := if hi : i = last k then b else
    F.orderEmbOfFin (α := α ×ₗ α) h (i.castPred hi) |>.1
