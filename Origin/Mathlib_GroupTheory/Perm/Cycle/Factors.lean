/-
Extracted from GroupTheory/Perm/Cycle/Factors.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Cycle factors of a permutation

Let `β` be a `Fintype` and `f : Equiv.Perm β`.

* `Equiv.Perm.cycleOf`: `f.cycleOf x` is the cycle of `f` that `x` belongs to.
* `Equiv.Perm.cycleFactors`: `f.cycleFactors` is a list of disjoint cyclic permutations
  that multiply to `f`.
-/

open Equiv Function Finset

variable {ι α β : Type*}

namespace Equiv.Perm

/-!
### `cycleOf`
-/

section CycleOf

variable {f g : Perm α} {x y : α}

def cycleOf (f : Perm α) [DecidableRel f.SameCycle] (x : α) : Perm α :=
  ofSubtype (subtypePerm f fun _ => sameCycle_apply_right : Perm { y // SameCycle f x y })

theorem cycleOf_apply (f : Perm α) [DecidableRel f.SameCycle] (x y : α) :
    cycleOf f x y = if SameCycle f x y then f y else y := by
  dsimp only [cycleOf]
  split_ifs with h
  · apply ofSubtype_apply_of_mem
    exact h
  · apply ofSubtype_apply_of_not_mem
    exact h

theorem cycleOf_inv (f : Perm α) [DecidableRel f.SameCycle] (x : α) :
    (cycleOf f x)⁻¹ = cycleOf f⁻¹ x :=
  Equiv.ext fun y => by
    rw [inv_eq_iff_eq, cycleOf_apply, cycleOf_apply]
    split_ifs <;> simp_all [sameCycle_inv, sameCycle_symm_apply_right]
