/-
Extracted from Order/ModularLattice.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Modular Lattices

This file defines (semi)modular lattices, a kind of lattice useful in algebra.
For examples, look to the subobject lattices of abelian groups, submodules, and ideals, or consider
any distributive lattice.

## Typeclasses

We define (semi)modularity typeclasses as Prop-valued mixins.

* `IsWeakUpperModularLattice`: Weakly upper modular lattices. Lattice where `a ⊔ b` covers `a`
  and `b` if `a` and `b` both cover `a ⊓ b`.
* `IsWeakLowerModularLattice`: Weakly lower modular lattices. Lattice where `a` and `b` cover
  `a ⊓ b` if `a ⊔ b` covers both `a` and `b`
* `IsUpperModularLattice`: Upper modular lattices. Lattices where `a ⊔ b` covers `a` if `b`
  covers `a ⊓ b`.
* `IsLowerModularLattice`: Lower modular lattices. Lattices where `a` covers `a ⊓ b` if `a ⊔ b`
  covers `b`.
- `IsModularLattice`: Modular lattices. Lattices where `a ≤ c → (a ⊔ b) ⊓ c = a ⊔ (b ⊓ c)`. We
  only require an inequality because the other direction holds in all lattices.

## Main Definitions

- `infIccOrderIsoIccSup` gives an order isomorphism between the intervals
  `[a ⊓ b, a]` and `[b, a ⊔ b]`.
  This corresponds to the diamond (or second) isomorphism theorems of algebra.

## Main Results

- `isModularLattice_iff_inf_sup_inf_assoc`:
  Modularity is equivalent to the `inf_sup_inf_assoc`: `(x ⊓ z) ⊔ (y ⊓ z) = ((x ⊓ z) ⊔ y) ⊓ z`
- `DistribLattice.isModularLattice`: Distributive lattices are modular.

## References

* [Manfred Stern, *Semimodular lattices. {Theory} and applications*][stern2009]
* [Wikipedia, *Modular Lattice*][https://en.wikipedia.org/wiki/Modular_lattice]

## TODO

- Relate atoms and coatoms in modular lattices
-/

open Set

variable {α : Type*}

class IsWeakUpperModularLattice (α : Type*) [Lattice α] : Prop where

  covBy_sup_of_inf_covBy_covBy {a b : α} : a ⊓ b ⋖ a → a ⊓ b ⋖ b → a ⋖ a ⊔ b
