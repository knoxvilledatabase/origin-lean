/-
Extracted from GroupTheory/SpecificGroups/KleinFour.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Klein Four Group

The Klein (Vierergruppe) four-group is a non-cyclic abelian group with four elements, in which
each element is self-inverse and in which composing any two of the three non-identity elements
produces the third one.

## Main definitions

* `IsKleinFour` : A mixin class which states that the group has order four and exponent two.
* `mulEquiv'` : An equivalence between a Klein four-group and a group of exponent two which
  preserves the identity is in fact an isomorphism.
* `mulEquiv`: Any two Klein four-groups are isomorphic via any identity-preserving equivalence.

## References

* https://en.wikipedia.org/wiki/Klein_four-group
* https://en.wikipedia.org/wiki/Alternating_group

## TODO

* Prove an `IsKleinFour` group is isomorphic to the normal subgroup of `alternatingGroup (Fin 4)`
  with the permutation cycles `V = {(), (1 2)(3 4), (1 3)(2 4), (1 4)(2 3)}`.  This is the kernel
  of the surjection of `alternatingGroup (Fin 4)` onto `alternatingGroup (Fin 3) ≃ (ZMod 3)`.
  In other words, we have the exact sequence `V → A₄ → A₃`.

* The outer automorphism group of `A₆` is the Klein four-group `V = (ZMod 2) × (ZMod 2)`,
  and is related to the outer automorphism of `S₆`. The extra outer automorphism in `A₆`
  swaps the 3-cycles (like `(1 2 3)`) with elements of shape `3²` (like `(1 2 3)(4 5 6)`).

## Tags
non-cyclic abelian group
-/

/-! ### Klein four-groups as a mixin class -/

class IsAddKleinFour (G : Type*) [AddGroup G] : Prop where
  card_four : Nat.card G = 4
  exponent_two : AddMonoid.exponent G = 2
