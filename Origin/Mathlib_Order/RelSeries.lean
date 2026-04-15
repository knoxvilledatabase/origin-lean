/-
Extracted from Order/RelSeries.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Series of a relation

If `r` is a relation on `α` then a relation series of length `n` is a series
`a_0, a_1, ..., a_n` such that `r a_i a_{i+1}` for all `i < n`

-/

open scoped SetRel

variable {α : Type*} (r : SetRel α α)

variable {β : Type*} (s : SetRel β β)

structure RelSeries where
  /-- The number of inequalities in the series -/
  length : ℕ
  /-- The underlying function of a relation series -/
  toFun : Fin (length + 1) → α
  /-- Adjacent elements are related -/
  step : ∀ (i : Fin length), toFun (Fin.castSucc i) ~[r] toFun i.succ

namespace RelSeries

-- INSTANCE (free from Core): :

{ coe := RelSeries.toFun }
