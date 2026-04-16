/-
Extracted from RingTheory/RootsOfUnity/EnoughRootsOfUnity.lean
Genuine: 4 | Conflates: 0 | Dissolved: 1 | Infrastructure: 2
-/
import Origin.Core
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

noncomputable section

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

instance rootsOfUnity_isCyclic (M : Type*) [CommMonoid M] (n : ℕ) [HasEnoughRootsOfUnity M n] :
    IsCyclic (rootsOfUnity n M) :=
  HasEnoughRootsOfUnity.cyc

-- DISSOLVED: of_dvd

instance finite_rootsOfUnity (M : Type*) [CommMonoid M] (n : ℕ) [NeZero n]
    [HasEnoughRootsOfUnity M n] :
    Finite <| rootsOfUnity n M := by
  have := rootsOfUnity_isCyclic M n
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := rootsOfUnity n M)
  have hg' : g ^ n = 1 := OneMemClass.coe_eq_one.mp g.prop
  let f (j : ZMod n) : rootsOfUnity n M := g ^ (j.val : ℤ)
  refine Finite.of_surjective f fun x ↦ ?_
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp <| hg x
  refine ⟨k, ?_⟩
  simpa only [ZMod.natCast_val, ← hk, f, ZMod.coe_intCast] using (zpow_eq_zpow_emod' k hg').symm

lemma natCard_rootsOfUnity (M : Type*) [CommMonoid M] (n : ℕ) [NeZero n]
    [HasEnoughRootsOfUnity M n] :
    Nat.card (rootsOfUnity n M) = n := by
  obtain ⟨ζ, h⟩ := exists_primitiveRoot M n
  rw [← IsCyclic.exponent_eq_card]
  refine dvd_antisymm ?_ ?_
  · exact Monoid.exponent_dvd_of_forall_pow_eq_one fun g ↦ OneMemClass.coe_eq_one.mp g.prop
  · nth_rewrite 1 [h.eq_orderOf]
    rw [← (h.isUnit <| NeZero.pos n).unit_spec, orderOf_units]
    let ζ' : rootsOfUnity n M := ⟨(h.isUnit <| NeZero.pos n).unit, ?_⟩
    · rw [← Subgroup.orderOf_mk]
      exact Monoid.order_dvd_exponent ζ'
    simp only [mem_rootsOfUnity, PNat.mk_coe]
    rw [← Units.eq_iff, Units.val_pow_eq_pow_val, IsUnit.unit_spec, h.pow_eq_one, Units.val_one]

end HasEnoughRootsOfUnity

section cyclic

lemma IsCyclic.monoidHom_equiv_self (G M : Type*) [CommGroup G] [Finite G]
    [IsCyclic G] [CommMonoid M] [HasEnoughRootsOfUnity M (Nat.card G)] :
    Nonempty ((G →* Mˣ) ≃* G) := by
  have : NeZero (Nat.card G) := ⟨Nat.card_pos.ne'⟩
  have hord := HasEnoughRootsOfUnity.natCard_rootsOfUnity M (Nat.card G)
  let e := (IsCyclic.monoidHom_mulEquiv_rootsOfUnity G Mˣ).some
  exact ⟨e.trans (rootsOfUnityUnitsMulEquiv M (Nat.card G)) |>.trans (mulEquivOfCyclicCardEq hord)⟩

end cyclic
