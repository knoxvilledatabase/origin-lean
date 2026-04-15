/-
Extracted from Algebra/Lie/Semisimple/Defs.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

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

variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M] [LieRingModule L M]

abbrev LieModule.IsIrreducible : Prop :=
  IsSimpleOrder (LieSubmodule R L M)

variable {R L M} in

lemma LieModule.IsIrreducible.mk [Nontrivial M] (h : ∀ N : LieSubmodule R L M, N ≠ ⊥ → N = ⊤) :
    IsIrreducible R L M :=
  IsSimpleOrder.of_forall_eq_top h

lemma LieSubmodule.eq_top_of_isIrreducible [LieModule.IsIrreducible R L M]
    (N : LieSubmodule R L M) [Nontrivial N] :
    N = ⊤ :=
  (IsSimpleOrder.eq_bot_or_eq_top N).resolve_left <| (nontrivial_iff_ne_bot R L M).mp inferInstance

namespace LieAlgebra

variable [LieAlgebra R L]
