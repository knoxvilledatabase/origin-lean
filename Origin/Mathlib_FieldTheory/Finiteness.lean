/-
Extracted from FieldTheory/Finiteness.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# A module over a division ring is Noetherian if and only if it is finite.

-/

universe u v

open Cardinal Submodule Module Function

namespace IsNoetherian

variable {K : Type u} {V : Type v} [DivisionRing K] [AddCommGroup V] [Module K V]

theorem iff_rank_lt_aleph0 : IsNoetherian K V ↔ Module.rank K V < ℵ₀ := by
  let b := Basis.ofVectorSpace K V
  rw [← b.mk_eq_rank'', lt_aleph0_iff_set_finite]
  constructor
  · intro
    exact (Basis.ofVectorSpaceIndex.linearIndependent K V).set_finite_of_isNoetherian
  · intro hbfinite
    refine
      @isNoetherian_of_linearEquiv K K (⊤ : Submodule K V) V _ _ _ _ _ _ (RingHom.id K) _ _ _
        (LinearEquiv.ofTop _ rfl) (id ?_)
    refine isNoetherian_of_fg_of_noetherian _ ⟨Set.Finite.toFinset hbfinite, ?_⟩
    rw [Set.Finite.coe_toFinset, ← b.span_eq, Basis.coe_ofVectorSpace, Subtype.range_coe]
