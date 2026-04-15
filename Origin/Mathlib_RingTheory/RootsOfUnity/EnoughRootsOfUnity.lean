/-
Extracted from RingTheory/RootsOfUnity/EnoughRootsOfUnity.lean
Genuine: 3 of 11 | Dissolved: 4 | Infrastructure: 4
-/
import Origin.Core

/-!
# Commutative monoids with enough roots of unity

We define a typeclass `HasEnoughRootsOfUnity M n` for a commutative monoid `M` and
a natural number `n` that asserts that `M` contains a primitive `n`th root of unity
and that the group of `n`th roots of unity in `M` is cyclic. Such monoids are suitable
targets for homomorphisms from groups of exponent (dividing) `n`; for example,
the homomorphisms can then be used to separate elements of the source group.
-/

class HasEnoughRootsOfUnity (M : Type*) [CommMonoid M] (n : ℕ) where
  prim : ∃ m : M, IsPrimitiveRoot m n
  cyc : IsCyclic <| rootsOfUnity n M

namespace HasEnoughRootsOfUnity

lemma exists_primitiveRoot (M : Type*) [CommMonoid M] (n : ℕ) [HasEnoughRootsOfUnity M n] :
    ∃ ζ : M, IsPrimitiveRoot ζ n :=
  HasEnoughRootsOfUnity.prim

-- INSTANCE (free from Core): rootsOfUnity_isCyclic

-- DISSOLVED: of_dvd

-- INSTANCE (free from Core): finite_rootsOfUnity

-- DISSOLVED: natCard_rootsOfUnity

-- DISSOLVED: of_card_le

end HasEnoughRootsOfUnity

-- DISSOLVED: MulEquiv.hasEnoughRootsOfUnity

section cyclic

lemma IsCyclic.monoidHom_equiv_self (G M : Type*) [CommGroup G] [Finite G]
    [IsCyclic G] [CommMonoid M] [HasEnoughRootsOfUnity M (Nat.card G)] :
    Nonempty ((G →* Mˣ) ≃* G) := by
  have : NeZero (Nat.card G) := ⟨Nat.card_pos.ne'⟩
  have hord := HasEnoughRootsOfUnity.natCard_rootsOfUnity M (Nat.card G)
  let e := (IsCyclic.monoidHom_mulEquiv_rootsOfUnity G Mˣ).some
  exact ⟨e.trans (rootsOfUnityUnitsMulEquiv M (Nat.card G)) |>.trans (mulEquivOfCyclicCardEq hord)⟩

end cyclic

-- INSTANCE (free from Core): {M

-- INSTANCE (free from Core): {G
