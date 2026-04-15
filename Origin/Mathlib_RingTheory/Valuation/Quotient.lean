/-
Extracted from RingTheory/Valuation/Quotient.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The valuation on a quotient ring

The support of a valuation `v : Valuation R Γ₀` is `supp v`. If `J` is an ideal of `R`
with `h : J ⊆ supp v` then the induced valuation
on `R / J` = `Ideal.Quotient J` is `onQuot v h`.

-/

namespace Valuation

variable {R Γ₀ : Type*} [CommRing R] [LinearOrderedCommMonoidWithZero Γ₀]

variable (v : Valuation R Γ₀)

def onQuotVal {J : Ideal R} (hJ : J ≤ supp v) : R ⧸ J → Γ₀ := fun q =>
  Quotient.liftOn' q v fun a b h =>
    calc
      v a = v (b + -(-a + b)) := by simp
      _ = v b :=
        v.map_add_supp b <| (Ideal.neg_mem_iff _).2 <| hJ <| QuotientAddGroup.leftRel_apply.mp h

def onQuot {J : Ideal R} (hJ : J ≤ supp v) : Valuation (R ⧸ J) Γ₀ where
  toFun := v.onQuotVal hJ
  map_zero' := v.map_zero
  map_one' := v.map_one
  map_mul' xbar ybar := Quotient.ind₂' v.map_mul xbar ybar
  map_add_le_max' xbar ybar := Quotient.ind₂' v.map_add xbar ybar
