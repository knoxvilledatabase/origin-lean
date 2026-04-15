/-
Extracted from Algebra/Lie/Semisimple/Basic.lean
Genuine: 9 of 12 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Semisimple Lie algebras

The famous Cartan-Dynkin-Killing classification of semisimple Lie algebras renders them one of the
most important classes of Lie algebras. In this file we prove basic results
about simple and semisimple Lie algebras.

## Main declarations

* `LieAlgebra.IsSemisimple.instHasTrivialRadical`: A semisimple Lie algebra has trivial radical.
* `LieAlgebra.IsSemisimple.instBooleanAlgebra`:
  The lattice of ideals in a semisimple Lie algebra is a Boolean algebra.
  In particular, this implies that the lattice of ideals is atomistic:
  every ideal is a direct sum of atoms (simple ideals) in a unique way.
* `LieAlgebra.hasTrivialRadical_iff_no_solvable_ideals`
* `LieAlgebra.hasTrivialRadical_iff_no_abelian_ideals`
* `LieAlgebra.abelian_radical_iff_solvable_is_abelian`

## Tags

lie algebra, radical, simple, semisimple
-/

section Irreducible

variable (R L M : Type*) [CommRing R] [LieRing L] [AddCommGroup M] [Module R M] [LieRingModule L M]

lemma LieModule.nontrivial_of_isIrreducible [LieModule.IsIrreducible R L M] : Nontrivial M where
  exists_pair_ne := by
    have aux : (⊥ : LieSubmodule R L M) ≠ ⊤ := bot_ne_top
    contrapose! aux
    ext m
    simpa using aux m 0

end Irreducible

namespace LieAlgebra

variable (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]

variable {R L} in

theorem HasTrivialRadical.eq_bot_of_isSolvable [HasTrivialRadical R L]
    (I : LieIdeal R L) [hI : IsSolvable I] : I = ⊥ :=
  sSup_eq_bot.mp radical_eq_bot _ hI

set_option backward.isDefEq.respectTransparency false in

-- INSTANCE (free from Core): [HasTrivialRadical

variable {R L} in

theorem hasTrivialRadical_of_no_solvable_ideals (h : ∀ I : LieIdeal R L, IsSolvable I → I = ⊥) :
    HasTrivialRadical R L :=
  ⟨sSup_eq_bot.mpr h⟩

theorem hasTrivialRadical_iff_no_solvable_ideals :
    HasTrivialRadical R L ↔ ∀ I : LieIdeal R L, IsSolvable I → I = ⊥ :=
  ⟨@HasTrivialRadical.eq_bot_of_isSolvable _ _ _ _ _, hasTrivialRadical_of_no_solvable_ideals⟩

set_option backward.isDefEq.respectTransparency false in

theorem hasTrivialRadical_iff_no_abelian_ideals :
    HasTrivialRadical R L ↔ ∀ I : LieIdeal R L, IsLieAbelian I → I = ⊥ := by
  rw [hasTrivialRadical_iff_no_solvable_ideals]
  constructor <;> intro h₁ I h₂
  · exact h₁ _ <| LieAlgebra.ofAbelianIsSolvable I
  · rw [← abelian_of_solvable_ideal_eq_bot_iff]
    exact h₁ _ <| abelian_derivedAbelianOfIdeal I

namespace IsSimple

variable [IsSimple R L]

-- INSTANCE (free from Core): :

protected lemma isAtom_top : IsAtom (⊤ : LieIdeal R L) := isAtom_top

variable {R L} in

protected lemma isAtom_iff_eq_top (I : LieIdeal R L) : IsAtom I ↔ I = ⊤ := isAtom_iff_eq_top

variable {R L} in

lemma eq_top_of_isAtom (I : LieIdeal R L) (hI : IsAtom I) : I = ⊤ := isAtom_iff_eq_top.mp hI

set_option backward.isDefEq.respectTransparency false in

-- INSTANCE (free from Core): :

end IsSimple

lemma isSimple_iff_of_not_isLieAbelian (hL : ¬ IsLieAbelian L) :
    IsSimpleOrder (LieIdeal R L) ↔ IsSimple R L :=
  ⟨fun _ ↦ ⟨IsSimpleOrder.eq_bot_or_eq_top, hL⟩, fun _ ↦ inferInstance⟩
