/-
Extracted from LinearAlgebra/FiniteDimensional/Basic.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Finite-dimensional vector spaces

Basic properties of finite-dimensional vector spaces, of their dimensions, and
of linear maps on such spaces.

## Main definitions

Preservation of finite-dimensionality and formulas for the dimension are given for
- submodules (`FiniteDimensional.finiteDimensional_submodule`)
- quotients (for the dimension of a quotient, see `Submodule.finrank_quotient_add_finrank` in
  `Mathlib/LinearAlgebra/Dimension/RankNullity.lean`)
- linear equivs, in `LinearEquiv.finiteDimensional`

Basic properties of linear maps of a finite-dimensional vector space are given. Notably, the
equivalence of injectivity and surjectivity is proved in `LinearMap.injective_iff_surjective`,
and the equivalence between left-inverse and right-inverse in `LinearMap.mul_eq_one_comm`
and `LinearMap.comp_eq_id_comm`.

## Implementation notes

You should not assume that there has been any effort to state lemmas as generally as possible.

Plenty of the results hold for general finitely generated modules (see
`Mathlib/RingTheory/Finiteness/Basic.lean`) or Noetherian modules (see
`Mathlib/RingTheory/Noetherian/Basic.lean`).
-/

universe u v v' w

open Cardinal Function IsNoetherian Module Submodule

variable {K : Type u} {V : Type v}

namespace FiniteDimensional

section DivisionRing

variable [DivisionRing K] [AddCommGroup V] [Module K V] {V₂ : Type v'} [AddCommGroup V₂]
  [Module K V₂]

theorem _root_.Submodule.eq_top_of_finrank_eq [FiniteDimensional K V] {S : Submodule K V}
    (h : finrank K S = finrank K V) : S = ⊤ := by
  set bS := Basis.ofVectorSpace K S with bS_eq
  have : LinearIndepOn K id (Subtype.val '' Basis.ofVectorSpaceIndex K S) := by
    simpa [bS] using bS.linearIndependent.linearIndepOn_id.image
      (f := Submodule.subtype S) (by simp)
  set b := Basis.extend this with b_eq
  letI i2 : Fintype (((↑) : S → V) '' Basis.ofVectorSpaceIndex K S) :=
    (LinearIndependent.set_finite_of_isNoetherian this).fintype
  have : (↑) '' Basis.ofVectorSpaceIndex K S = this.extend (Set.subset_univ _) :=
    Set.eq_of_subset_of_card_le (this.subset_extend _)
      (by
        rw [Set.card_image_of_injective _ Subtype.coe_injective, ← finrank_eq_card_basis bS, ←
            finrank_eq_card_basis b, h])
  rw [← b.span_eq, b_eq, Basis.coe_extend, Subtype.range_coe, ← this, ← Submodule.coe_subtype,
    span_image]
  have := bS.span_eq
  rw [bS_eq, Basis.coe_ofVectorSpace, Subtype.range_coe] at this
  rw [this, Submodule.map_top (Submodule.subtype S), range_subtype]

open Finset

variable {L : Type*} [Field L] [LinearOrder L] [IsStrictOrderedRing L]

variable {W : Type v} [AddCommGroup W] [Module L W]

theorem exists_relation_sum_zero_pos_coefficient_of_finrank_succ_lt_card [FiniteDimensional L W]
    {t : Finset W} (h : finrank L W + 1 < t.card) :
    ∃ f : W → L, ∑ e ∈ t, f e • e = 0 ∧ ∑ e ∈ t, f e = 0 ∧ ∃ x ∈ t, 0 < f x := by
  obtain ⟨f, sum, total, nonzero⟩ :=
    Module.exists_nontrivial_relation_sum_zero_of_finrank_succ_lt_card h
  exact ⟨f, sum, total, exists_pos_of_sum_zero_of_exists_nonzero f total nonzero⟩

end
