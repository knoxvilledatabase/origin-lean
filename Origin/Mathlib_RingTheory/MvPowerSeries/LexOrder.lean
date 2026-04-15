/-
Extracted from RingTheory/MvPowerSeries/LexOrder.lean
Genuine: 1 of 2 | Dissolved: 1 | Infrastructure: 0
-/
import Origin.Core

/-! LexOrder of multivariate power series

Given an ordering of `σ` such that `WellOrderGT σ`,
the lexicographic order on `σ →₀ ℕ` is a well ordering,
which can be used to define a natural valuation `lexOrder` on the ring `MvPowerSeries σ R`:
the smallest exponent in the support.

-/

namespace MvPowerSeries

variable {σ R : Type*}

variable [Semiring R]

section LexOrder

open Finsupp

variable [LinearOrder σ] [WellFoundedGT σ]

set_option backward.isDefEq.respectTransparency false in

noncomputable def lexOrder (φ : MvPowerSeries σ R) : (WithTop (Lex (σ →₀ ℕ))) := by
  classical
  exact if h : φ = 0 then ⊤ else by
    have ne : Set.Nonempty (toLex '' φ.support) := by
      simp only [Set.image_nonempty, Function.support_nonempty_iff, ne_eq, h, not_false_eq_true]
    apply WithTop.some
    apply WellFounded.min _ (toLex '' φ.support) ne
    · exact Finsupp.instLTLex.lt
    · exact wellFounded_lt

set_option backward.isDefEq.respectTransparency false in

-- DISSOLVED: lexOrder_def_of_ne_zero
