/-
Extracted from Algebra/Lie/Semisimple/Defs.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Algebra.Lie.Solvable

/-!
# Semisimple Lie algebras

In this file we define simple and semisimple Lie algebras, together with related concepts.

## Main declarations

* `LieModule.IsIrreducible`
* `LieAlgebra.IsSimple`
* `LieAlgebra.HasTrivialRadical`
* `LieAlgebra.IsSemisimple`

## Tags

lie algebra, radical, simple, semisimple
-/

variable (R L M : Type*)

variable [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M] [LieRingModule L M]

abbrev LieModule.IsIrreducible : Prop :=
  IsSimpleOrder (LieSubmodule R L M)

namespace LieAlgebra

class HasTrivialRadical : Prop where
  radical_eq_bot : radical R L = ⊥

export HasTrivialRadical (radical_eq_bot)

attribute [simp] radical_eq_bot

class IsSimple : Prop where
  eq_bot_or_eq_top : ∀ I : LieIdeal R L, I = ⊥ ∨ I = ⊤
  non_abelian : ¬IsLieAbelian L

class IsSemisimple : Prop where
  /-- In a semisimple Lie algebra, the supremum of the atoms is the whole Lie algebra. -/
  sSup_atoms_eq_top : sSup {I : LieIdeal R L | IsAtom I} = ⊤
  /-- In a semisimple Lie algebra, the atoms are independent. -/
  sSupIndep_isAtom : sSupIndep {I : LieIdeal R L | IsAtom I}
  /-- In a semisimple Lie algebra, the atoms are non-abelian. -/
  non_abelian_of_isAtom : ∀ I : LieIdeal R L, IsAtom I → ¬ IsLieAbelian I

end LieAlgebra
