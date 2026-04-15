/-
Extracted from Data/EReal/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The extended real numbers

This file defines `EReal`, `ℝ` with a top element `⊤` and a bottom element `⊥`, implemented as
`WithBot (WithTop ℝ)`.

`EReal` is a `CompleteLinearOrder`, deduced by typeclass inference from the fact that
`WithBot (WithTop L)` completes a conditionally complete linear order `L`.

Coercions from `ℝ` (called `coe` in lemmas) and from `ℝ≥0∞` (`coe_ennreal`) are registered
and their basic properties proved. The latter takes up most of the rest of this file.

## Tags

real, ereal, complete lattice
-/

open Function ENNReal NNReal Set

noncomputable section

def EReal := WithBot (WithTop ℝ)

deriving Nontrivial,

  Zero, One, AddMonoid, AddCommMonoid, AddCommMonoidWithOne, CharZero,

  Top, Bot, SupSet, InfSet, PartialOrder, LinearOrder, CompleteLinearOrder, DenselyOrdered,

  ZeroLEOneClass, IsOrderedAddMonoid
