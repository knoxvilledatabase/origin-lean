/-
Extracted from SetTheory/Ordinal/FixedPointApproximants.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Ordinal Approximants for the Fixed points on complete lattices

This file sets up the ordinal-indexed approximation theory of fixed points
of a monotone function in a complete lattice [Cousot1979].
The proof follows loosely the one from [Echenique2005].

However, the proof given here is not constructive as we use the non-constructive axiomatization of
ordinals from mathlib. It still allows an approximation scheme indexed over the ordinals.

## Main definitions

* `OrdinalApprox.lfpApprox`: The ordinal-indexed approximation of the least fixed point
  greater or equal than an initial value of a bundled monotone function.
* `OrdinalApprox.gfpApprox`: The ordinal-indexed approximation of the greatest fixed point
  less or equal than an initial value of a bundled monotone function.

## Main theorems
* `OrdinalApprox.lfp_mem_range_lfpApprox`: The ordinal-indexed approximation of
  the least fixed point eventually reaches the least fixed point
* `OrdinalApprox.gfp_mem_range_gfpApprox`: The ordinal-indexed approximation of
  the greatest fixed point eventually reaches the greatest fixed point

## References
* [F. Echenique, *A short and constructive proof of Tarski’s fixed-point theorem*][Echenique2005]
* [P. Cousot & R. Cousot, *Constructive Versions of Tarski's Fixed Point Theorems*][Cousot1979]

## Tags

fixed point, complete lattice, monotone function, ordinals, approximation
-/

namespace Cardinal

universe u

variable {α : Type u}

variable (g : Ordinal → α)

open Cardinal Ordinal SuccOrder Function Set

theorem not_injective_limitation_set : ¬ InjOn g (Iio (ord <| succ #α)) := by
  intro h_inj
  have h := lift_mk_le_lift_mk_of_injective <| injOn_iff_injective.1 h_inj
  have mk_initialSeg_subtype :
      #(Iio (ord <| succ #α)) = lift.{u + 1} (succ #α) := by
    simpa only [coe_setOf, card_typein, card_ord] using mk_Iio_ordinal (ord <| succ #α)
  rw [mk_initialSeg_subtype, lift_lift, lift_le] at h
  exact not_le_of_gt (Order.lt_succ #α) h

end Cardinal

namespace OrdinalApprox

universe u

variable {α : Type u}

variable [CompleteLattice α] (f : α →o α) {x : α} {a b c : Ordinal.{u}}

open Function fixedPoints Cardinal Order OrderHom

variable (x) in

def lfpApprox (a : Ordinal.{u}) : α :=
  x ⊔ ⨆ b < a, f (lfpApprox b)

termination_by a

theorem lfpApprox_mono_right : Monotone (lfpApprox f x) := by
  intro a b h
  rw [lfpApprox, lfpApprox]
  apply sup_le_sup_left (iSup₂_mono' _)
  grind
