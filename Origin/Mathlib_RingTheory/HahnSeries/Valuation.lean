/-
Extracted from RingTheory/HahnSeries/Valuation.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Valuations on Hahn Series rings
If `Γ` is a `LinearOrderedCancelAddCommMonoid` and `R` is a domain, then the domain `R⟦Γ⟧`
admits an additive valuation given by `orderTop`.

## Main Definitions
* `HahnSeries.addVal Γ R` defines an `AddValuation` on `R⟦Γ⟧` when `Γ` is linearly
  ordered.

## TODO
* Multiplicative valuations
* Add any API for Laurent series valuations that do not depend on `Γ = ℤ`.

## References
- [J. van der Hoeven, *Operators on Generalized Power Series*][van_der_hoeven]
-/

noncomputable section

variable {Γ R : Type*}

namespace HahnSeries

section Valuation

variable [AddCancelCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ] [Ring R] [IsDomain R]

variable (Γ R) in

def addVal : AddValuation R⟦Γ⟧ (WithTop Γ) :=
  AddValuation.of orderTop orderTop_zero (orderTop_one) (fun _ _ => min_orderTop_le_orderTop_add)
  fun x y => by
    by_cases hx : x = 0; · simp [hx]
    by_cases hy : y = 0; · simp [hy]
    rw [← order_eq_orderTop_of_ne_zero hx, ← order_eq_orderTop_of_ne_zero hy,
      ← order_eq_orderTop_of_ne_zero (mul_ne_zero hx hy), ← WithTop.coe_add, WithTop.coe_eq_coe,
      order_mul hx hy]

theorem addVal_apply {x : R⟦Γ⟧} : addVal Γ R x = x.orderTop :=
  AddValuation.of_apply _
