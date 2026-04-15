/-
Extracted from LinearAlgebra/FiniteDimensional/Lemmas.lean
Genuine: 14 of 14 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Finite-dimensional vector spaces

This file contains some further development of finite-dimensional vector spaces, their dimensions,
and linear maps on such spaces.

Definitions are in `Mathlib/LinearAlgebra/FiniteDimensional/Defs.lean`
and results that require fewer imports are in `Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean`.
-/

assert_not_exists Monoid.exponent Module.IsTorsion

universe u v v'

open Cardinal Submodule Module Function

variable {K : Type u} {V : Type v}

namespace Submodule

open IsNoetherian Module

section DivisionRing

variable [DivisionRing K] [AddCommGroup V] [Module K V]

theorem finrank_lt [FiniteDimensional K V] {s : Submodule K V} (h : s ≠ ⊤) :
    finrank K s < finrank K V := by
  rw [← s.finrank_quotient_add_finrank, add_comm]
  rw [← Quotient.nontrivial_iff] at h
  exact Nat.lt_add_of_pos_right finrank_pos

theorem finrank_sup_add_finrank_inf_eq (s t : Submodule K V) [FiniteDimensional K s]
    [FiniteDimensional K t] :
    finrank K ↑(s ⊔ t) + finrank K ↑(s ⊓ t) = finrank K ↑s + finrank K ↑t := by
  have key : Module.rank K ↑(s ⊔ t) + Module.rank K ↑(s ⊓ t) = Module.rank K s + Module.rank K t :=
    rank_sup_add_rank_inf_eq s t
  repeat rw [← finrank_eq_rank] at key
  norm_cast at key

theorem finrank_add_le_finrank_add_finrank (s t : Submodule K V) [FiniteDimensional K s]
    [FiniteDimensional K t] : finrank K (s ⊔ t : Submodule K V) ≤ finrank K s + finrank K t := by
  rw [← finrank_sup_add_finrank_inf_eq]
  exact self_le_add_right _ _

theorem finrank_add_finrank_le_of_disjoint [FiniteDimensional K V]
    {s t : Submodule K V} (hdisjoint : Disjoint s t) :
    finrank K s + finrank K t ≤ finrank K V := by
  rw [← Submodule.finrank_sup_add_finrank_inf_eq s t, hdisjoint.eq_bot, finrank_bot, add_zero]
  exact Submodule.finrank_le _

theorem eq_top_of_disjoint [FiniteDimensional K V] (s t : Submodule K V)
    (hdim : finrank K V ≤ finrank K s + finrank K t) (hdisjoint : Disjoint s t) : s ⊔ t = ⊤ := by
  have h_finrank_inf : finrank K ↑(s ⊓ t) = 0 := by
    rw [disjoint_iff_inf_le, le_bot_iff] at hdisjoint
    rw [hdisjoint, finrank_bot]
  apply eq_top_of_finrank_eq
  replace hdim : finrank K V = finrank K s + finrank K t :=
    le_antisymm hdim (finrank_add_finrank_le_of_disjoint hdisjoint)
  rw [hdim]
  convert s.finrank_sup_add_finrank_inf_eq t
  rw [h_finrank_inf, add_zero]

theorem isCompl_iff_disjoint [FiniteDimensional K V] (s t : Submodule K V)
    (hdim : finrank K V ≤ finrank K s + finrank K t) :
    IsCompl s t ↔ Disjoint s t :=
  ⟨fun h ↦ h.1, fun h ↦ ⟨h, codisjoint_iff.mpr <| eq_top_of_disjoint s t hdim h⟩⟩

theorem sup_span_singleton_eq_top_iff [Module.Finite K V] {W : Submodule K V} {v : V} (hv : v ∉ W) :
    W ⊔ span K {v} = ⊤ ↔ finrank K (V ⧸ W) = 1 := by
  refine ⟨fun hW ↦ ?_, fun hW ↦ ?_⟩
  · suffices W ⊓ span K {v} = ⊥ by
      have hv₀ : v ≠ 0 := by aesop
      have aux := finrank_sup_add_finrank_inf_eq W (span K {v})
      rw [hW, finrank_span_singleton hv₀, this, finrank_bot, finrank_top,
        ← finrank_quotient_add_finrank W] at aux
      lia
    refine (Submodule.eq_bot_iff _).mpr fun w hw ↦ ?_
    obtain ⟨ht, t, rfl⟩ : w ∈ W ∧ ∃ t : K, t • v = w := by simpa [mem_span_singleton] using hw
    rcases eq_or_ne t 0 with rfl | ht₀; · simp
    rw [Submodule.smul_mem_iff _ ht₀] at ht
    contradiction
  · apply Submodule.eq_top_of_disjoint
    · rw [← W.finrank_quotient_add_finrank, add_comm, add_le_add_iff_left, hW]
      aesop
    · exact Submodule.disjoint_span_singleton_of_notMem hv

end DivisionRing

end Submodule

namespace FiniteDimensional

section DivisionRing

variable [DivisionRing K] [AddCommGroup V] [Module K V] {V₂ : Type v'} [AddCommGroup V₂]
  [Module K V₂]

variable [FiniteDimensional K V] [FiniteDimensional K V₂]

noncomputable def LinearEquiv.quotEquivOfEquiv {p : Subspace K V} {q : Subspace K V₂}
    (f₁ : p ≃ₗ[K] q) (f₂ : V ≃ₗ[K] V₂) : (V ⧸ p) ≃ₗ[K] V₂ ⧸ q :=
  LinearEquiv.ofFinrankEq _ _
    (by
      rw [← @add_right_cancel_iff _ _ _ (finrank K p), Submodule.finrank_quotient_add_finrank,
        LinearEquiv.finrank_eq f₁, Submodule.finrank_quotient_add_finrank,
        LinearEquiv.finrank_eq f₂])

noncomputable def LinearEquiv.quotEquivOfQuotEquiv {p q : Subspace K V} (f : (V ⧸ p) ≃ₗ[K] q) :
    (V ⧸ q) ≃ₗ[K] p :=
  LinearEquiv.ofFinrankEq _ _ <| by
    rw [← add_right_cancel_iff, Submodule.finrank_quotient_add_finrank, ← LinearEquiv.finrank_eq f,
      add_comm, Submodule.finrank_quotient_add_finrank]

end DivisionRing

end FiniteDimensional

namespace LinearMap

open Module

section DivisionRing

variable [DivisionRing K] [AddCommGroup V] [Module K V] {V₂ : Type v'} [AddCommGroup V₂]
  [Module K V₂]

theorem finrank_range_add_finrank_ker [FiniteDimensional K V] (f : V →ₗ[K] V₂) :
    finrank K (LinearMap.range f) + finrank K (LinearMap.ker f) = finrank K V := by
  rw [← f.quotKerEquivRange.finrank_eq]
  exact Submodule.finrank_quotient_add_finrank _

lemma ker_ne_bot_of_finrank_lt [FiniteDimensional K V] [FiniteDimensional K V₂] {f : V →ₗ[K] V₂}
    (h : finrank K V₂ < finrank K V) :
    LinearMap.ker f ≠ ⊥ := by
  have h₁ := f.finrank_range_add_finrank_ker
  have h₂ : finrank K (LinearMap.range f) ≤ finrank K V₂ := (LinearMap.range f).finrank_le
  suffices 0 < finrank K (LinearMap.ker f) from Submodule.one_le_finrank_iff.mp this
  lia

end DivisionRing

end LinearMap

open Module

namespace LinearMap

variable [DivisionRing K] [AddCommGroup V] [Module K V] {V₂ : Type v'} [AddCommGroup V₂]
  [Module K V₂]

theorem injective_iff_surjective_of_finrank_eq_finrank [FiniteDimensional K V]
    [FiniteDimensional K V₂] (H : finrank K V = finrank K V₂) {f : V →ₗ[K] V₂} :
    Function.Injective f ↔ Function.Surjective f := by
  have := finrank_range_add_finrank_ker f
  rw [← ker_eq_bot, ← range_eq_top]; refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [h, finrank_bot, add_zero, H] at this
    exact eq_top_of_finrank_eq this
  · rw [h, finrank_top, H] at this
    exact Submodule.finrank_eq_zero.1 (add_right_injective _ this)

theorem ker_eq_bot_iff_range_eq_top_of_finrank_eq_finrank [FiniteDimensional K V]
    [FiniteDimensional K V₂] (H : finrank K V = finrank K V₂) {f : V →ₗ[K] V₂} :
    LinearMap.ker f = ⊥ ↔ LinearMap.range f = ⊤ := by
  rw [range_eq_top, ker_eq_bot, injective_iff_surjective_of_finrank_eq_finrank H]

noncomputable def linearEquivOfInjective [FiniteDimensional K V] [FiniteDimensional K V₂]
    (f : V →ₗ[K] V₂) (hf : Injective f) (hdim : finrank K V = finrank K V₂) : V ≃ₗ[K] V₂ :=
  LinearEquiv.ofBijective f
    ⟨hf, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hf⟩
