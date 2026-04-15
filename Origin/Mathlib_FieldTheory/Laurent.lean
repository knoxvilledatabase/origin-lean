/-
Extracted from FieldTheory/Laurent.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Laurent expansions of rational functions

## Main declarations

* `RatFunc.laurent`: the Laurent expansion of the rational function `f` at `r`, as an `AlgHom`.
* `RatFunc.laurent_injective`: the Laurent expansion at `r` is unique

## Implementation details

Implemented as the quotient of two Taylor expansions, over domains.
An auxiliary definition is provided first to make the construction of the `AlgHom` easier,
  which works on `CommRing` which are not necessarily domains.
-/

universe u

namespace RatFunc

noncomputable section

open Polynomial

open scoped nonZeroDivisors

variable {R : Type u} [CommRing R] (r s : R) (p q : R[X]) (f : R⟮X⟯)

theorem taylor_mem_nonZeroDivisors (hp : p ∈ R[X]⁰) : taylor r p ∈ R[X]⁰ := by
  rw [mem_nonZeroDivisors_iff_right]
  intro x hx
  have : x = taylor (r - r) x := by simp
  rwa [this, sub_eq_add_neg, ← taylor_taylor, ← taylor_mul,
    LinearMap.map_eq_zero_iff _ (taylor_injective _), mul_right_mem_nonZeroDivisors_eq_zero_iff hp,
    LinearMap.map_eq_zero_iff _ (taylor_injective _)] at hx

def laurentAux : R⟮X⟯ →+* R⟮X⟯ :=
  RatFunc.mapRingHom
    ( { toFun := taylor r
        map_add' := map_add (taylor r)
        map_mul' := taylor_mul _
        map_zero' := map_zero (taylor r)
        map_one' := taylor_one r } : R[X] →+* R[X])
    (taylor_mem_nonZeroDivisors _)

theorem laurentAux_ofFractionRing_mk (q : R[X]⁰) :
    laurentAux r (ofFractionRing (Localization.mk p q)) =
      ofFractionRing (.mk (taylor r p) ⟨taylor r q, taylor_mem_nonZeroDivisors r q q.prop⟩) :=
  map_apply_ofFractionRing_mk _ _ _ _

variable [IsDomain R]

theorem laurentAux_div :
    laurentAux r (algebraMap _ _ p / algebraMap _ _ q) =
      algebraMap _ _ (taylor r p) / algebraMap _ _ (taylor r q) :=
  -- Porting note: added `by exact taylor_mem_nonZeroDivisors r`
  map_apply_div _ (by exact taylor_mem_nonZeroDivisors r) _ _
