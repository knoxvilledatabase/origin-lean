/-
Extracted from Data/Finset/Lattice/Pi.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Lattice operations on finsets of functions

This file is concerned with folding binary lattice operations over finsets.
-/

assert_not_exists IsOrderedMonoid MonoidWithZero

variable {α ι : Type*}

namespace Finset

variable [DistribLattice α] [BoundedOrder α] [DecidableEq ι]

theorem sup_inf {κ : ι → Type*} (s : Finset ι) (t : ∀ i, Finset (κ i)) (f : ∀ i, κ i → α) :
    (s.sup fun i => (t i).inf (f i)) = (s.pi t).inf fun g => s.attach.sup fun i => f _ <| g _ i.2 :=
  @inf_sup αᵒᵈ _ _ _ _ _ _ _ _

end Finset
