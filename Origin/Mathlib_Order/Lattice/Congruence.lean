/-
Extracted from Order/Lattice/Congruence.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Lattice Congruences

## Main definitions

- `LatticeCon`: An equivalence relation is a congruence relation for the lattice structure if it is
  compatible with the `inf` and `sup` operations.
- `LatticeCon.ker`: The kernel of a lattice homomorphism as a lattice congruence.

## Main statements

- `LatticeCon.mk'`: Alternative conditions for a relation to be a lattice congruence.

## References

* [Grätzer et al, *General lattice theory*][Graetzer2003]

## Tags

Lattice, Congruence
-/

variable {F α β : Type*} [Lattice α] [Lattice β]

variable (α) in

structure LatticeCon extends Setoid α where
  inf : ∀ {w x y z}, r w x → r y z → r (w ⊓ y) (x ⊓ z)
  sup : ∀ {w x y z}, r w x → r y z → r (w ⊔ y) (x ⊔ z)

namespace LatticeCon
