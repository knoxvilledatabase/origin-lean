/-
Extracted from NumberTheory/MulChar/Duality.lean
Genuine: 4 of 7 | Dissolved: 2 | Infrastructure: 1
-/
import Origin.Core

/-!
# Duality for multiplicative characters

Let `M` be a finite commutative monoid and `R` a ring that has enough `n`th roots of unity,
where `n` is the exponent of `M`. Then the main results of this file are as follows.

## Main results

* `MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity`: multiplicative characters
  `M → R` separate elements of `Mˣ`.

* `MulChar.mulEquiv_units`: the group of multiplicative characters `M → R` is
  (noncanonically) isomorphic to `Mˣ`.

* `MulChar.mulCharEquiv`: the `MulEquiv` between the double dual `MulChar (MulChar M R) R` of `M`
  and `Mˣ`.

* `MulChar.subgroupOrderIsoSubgroupMulChar`: The order reversing bijection that sends a
  subgroup of `Mˣ` to its dual subgroup in `MulChar M R`.

-/

namespace MulChar

variable {M R : Type*} [CommMonoid M] [CommRing R]

-- INSTANCE (free from Core): finite

-- DISSOLVED: exists_apply_ne_one_iff_exists_monoidHom

variable (M R)

variable [Finite M] [HasEnoughRootsOfUnity R (Monoid.exponent Mˣ)]

-- DISSOLVED: exists_apply_ne_one_of_hasEnoughRootsOfUnity

lemma mulEquiv_units : Nonempty (MulChar M R ≃* Mˣ) :=
  ⟨mulEquivToUnitHom.trans
    (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity Mˣ R).some⟩

lemma card_eq_card_units_of_hasEnoughRootsOfUnity : Nat.card (MulChar M R) = Nat.card Mˣ :=
  Nat.card_congr (mulEquiv_units M R).some.toEquiv

theorem restrictHom_surjective (N : Submonoid M) :
    Function.Surjective (MulChar.restrictHom N R) := by
  intro χ
  obtain ⟨ψ, hψ⟩ := (χ.toUnitHom.comp N.unitsEquivUnitsType).restrict_surjective R N.units
  refine ⟨MulChar.ofUnitHom ψ, ext fun _ ↦ ?_⟩
  rw [MonoidHom.restrictHom_apply] at hψ
  rw [restrictHom_apply, restrict_ofUnitHom]
  simp [hψ]

noncomputable def mulCharEquiv : MulChar (MulChar M R) R ≃* Mˣ :=
  mulEquivToUnitHom.trans <| toUnits.monoidHomCongrLeft.symm.trans <|
    mulEquivToUnitHom.monoidHomCongrLeft.trans <| CommGroup.monoidHomMonoidHomEquiv Mˣ R

variable {M R}
