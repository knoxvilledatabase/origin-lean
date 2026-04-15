/-
Extracted from LinearAlgebra/Dimension/DivisionRing.lean
Genuine: 3 of 4 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Dimension of vector spaces

In this file we provide results about `Module.rank` and `Module.finrank` of vector spaces
over division rings.

## Main statements

For vector spaces (i.e. modules over a field), we have

* `rank_quotient_add_rank_of_divisionRing`: if `V₁` is a submodule of `V`, then
  `Module.rank (V/V₁) + Module.rank V₁ = Module.rank V`.
* `rank_range_add_rank_ker`: the rank-nullity theorem.

See also `Mathlib/LinearAlgebra/Dimension/ErdosKaplansky.lean` for the Erdős-Kaplansky theorem.

-/

noncomputable section

universe u₀ u v v' v'' u₁' w w'

variable {K : Type u} {V V₁ V₂ V₃ : Type v}

variable {ι : Type w}

open Cardinal Basis Submodule Function Set

section Module

section DivisionRing

variable [DivisionRing K]

variable [AddCommGroup V] [Module K V]

variable [AddCommGroup V₁] [Module K V₁]

theorem Module.Basis.finite_ofVectorSpaceIndex_of_rank_lt_aleph0 (h : Module.rank K V < ℵ₀) :
    (Basis.ofVectorSpaceIndex K V).Finite :=
  Set.finite_def.2 <| (Basis.ofVectorSpace K V).nonempty_fintype_index_of_rank_lt_aleph0 h

theorem rank_quotient_add_rank_of_divisionRing (p : Submodule K V) :
    Module.rank K (V ⧸ p) + Module.rank K p = Module.rank K V := by
  classical
    let ⟨f⟩ := quotient_prod_linearEquiv p
    exact rank_prod'.symm.trans f.rank_eq

-- INSTANCE (free from Core): DivisionRing.hasRankNullity

variable [AddCommGroup V₂] [Module K V₂]

variable [AddCommGroup V₃] [Module K V₃]

open LinearMap

theorem rank_add_rank_split (db : V₂ →ₗ[K] V) (eb : V₃ →ₗ[K] V) (cd : V₁ →ₗ[K] V₂)
    (ce : V₁ →ₗ[K] V₃) (hde : ⊤ ≤ LinearMap.range db ⊔ LinearMap.range eb) (hgd : ker cd = ⊥)
    (eq : db.comp cd = eb.comp ce) (eq₂ : ∀ d e, db d = eb e → ∃ c, cd c = d ∧ ce c = e) :
    Module.rank K V + Module.rank K V₁ = Module.rank K V₂ + Module.rank K V₃ := by
  have hf : Surjective (coprod db eb) := by
    rwa [← range_eq_top, range_coprod, eq_top_iff]
  conv =>
    rhs
    rw [← rank_prod', rank_eq_of_surjective hf]
  congr 1
  apply LinearEquiv.rank_eq
  let L : V₁ →ₗ[K] ker (coprod db eb) :=
    LinearMap.codRestrict _ (prod cd (-ce)) <| by
      simpa [add_eq_zero_iff_eq_neg] using LinearMap.ext_iff.1 eq
  refine LinearEquiv.ofBijective L ⟨?_, ?_⟩
  · rw [← ker_eq_bot, ker_codRestrict, ker_prod, hgd, bot_inf_eq]
  · rw [← range_eq_top, eq_top_iff, LinearMap.range_codRestrict, ← map_le_iff_le_comap,
      Submodule.map_top, range_subtype]
    rintro ⟨d, e⟩
    have h := eq₂ d (-e)
    simp only [add_eq_zero_iff_eq_neg, LinearMap.prod_apply, mem_ker,
      Prod.mk_inj, coprod_apply, map_neg, neg_apply, LinearMap.mem_range, Pi.prod] at h ⊢
    grind

end

end DivisionRing

end Module
