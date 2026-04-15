/-
Extracted from NumberTheory/MulChar/Duality.lean
Genuine: 2 of 5 | Dissolved: 2 | Infrastructure: 1
-/
import Origin.Core
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.NumberTheory.MulChar.Basic

/-!
# Duality for multiplicative characters

Let `M` be a finite commutative monoid and `R` a ring that has enough `n`th roots of unity,
where `n` is the exponent of `M`. Then the main results of this file are as follows.

* `MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity`: multiplicative characters
  `M → R` separate elements of `Mˣ`.

* `MulChar.mulEquiv_units`: the group of multiplicative characters `M → R` is
   (noncanonically) isomorphic to `Mˣ`.
-/

namespace MulChar

variable {M R : Type*} [CommMonoid M] [CommRing R]

instance finite [Finite Mˣ] [IsDomain R] : Finite (MulChar M R) := by
  have : Finite (Mˣ →* Rˣ) := by
    have : Fintype Mˣ := .ofFinite _
    let S := rootsOfUnity (Fintype.card Mˣ) R
    let F := Mˣ →* S
    have fF : Finite F := .of_injective _ DFunLike.coe_injective
    refine .of_surjective (fun f : F ↦ (Subgroup.subtype _).comp f) fun f ↦ ?_
    have H a : f a ∈ S := by simp only [mem_rootsOfUnity, ← map_pow, pow_card_eq_one, map_one, S]
    refine ⟨.codRestrict f S H, MonoidHom.ext fun _ ↦ ?_⟩
    simp only [MonoidHom.coe_comp, Subgroup.coeSubtype, Function.comp_apply,
      MonoidHom.codRestrict_apply]
  exact .of_equiv _ MulChar.equivToUnitHom.symm

-- DISSOLVED: exists_apply_ne_one_iff_exists_monoidHom

variable (M R)

variable [Finite M] [HasEnoughRootsOfUnity R (Monoid.exponent Mˣ)]

-- DISSOLVED: exists_apply_ne_one_of_hasEnoughRootsOfUnity

lemma mulEquiv_units : Nonempty (MulChar M R ≃* Mˣ) :=
  ⟨mulEquivToUnitHom.trans
    (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity Mˣ R).some⟩

lemma card_eq_card_units_of_hasEnoughRootsOfUnity : Nat.card (MulChar M R) = Nat.card Mˣ :=
  Nat.card_congr (mulEquiv_units M R).some.toEquiv

end MulChar
