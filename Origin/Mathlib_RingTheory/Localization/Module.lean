/-
Extracted from RingTheory/Localization/Module.lean
Genuine: 6 of 6 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Modules / vector spaces over localizations / fraction fields

This file contains some results about vector spaces over the field of fractions of a ring.

## Main results

* `LinearIndependent.localization`: `b` is linear independent over a localization of `R`
  if it is linear independent over `R` itself
* `Basis.ofIsLocalizedModule` / `Basis.localizationLocalization`: promote an `R`-basis `b` of `A`
  to an `Rₛ`-basis of `Aₛ`, where `Rₛ` and `Aₛ` are localizations of `R` and `A` at `s`
  respectively
* `LinearIndependent.iff_fractionRing`: `b` is linear independent over `R` iff it is
  linear independent over `Frac(R)`
-/

open nonZeroDivisors

section Localization

variable {R : Type*} (Rₛ : Type*)

section IsLocalizedModule

open Submodule

variable [CommSemiring R] (S : Submonoid R) [CommSemiring Rₛ] [Algebra R Rₛ] [IsLocalization S Rₛ]
  {M Mₛ : Type*} [AddCommMonoid M] [Module R M] [AddCommMonoid Mₛ] [Module R Mₛ]
  [Module Rₛ Mₛ] [IsScalarTower R Rₛ Mₛ] (f : M →ₗ[R] Mₛ) [IsLocalizedModule S f]

include S

theorem span_eq_top_of_isLocalizedModule {v : Set M} (hv : span R v = ⊤) :
    span Rₛ (f '' v) = ⊤ := top_unique fun x _ ↦ by
  obtain ⟨⟨m, s⟩, h⟩ := IsLocalizedModule.surj S f x
  rw [Submonoid.smul_def, ← algebraMap_smul Rₛ, ← Units.smul_isUnit (IsLocalization.map_units Rₛ s),
    eq_comm, ← inv_smul_eq_iff] at h
  refine h ▸ smul_mem _ _ (span_subset_span R Rₛ _ ?_)
  rw [← LinearMap.coe_restrictScalars R, ← LinearMap.map_span, hv]
  exact mem_map_of_mem mem_top

theorem LinearIndependent.of_isLocalizedModule {ι : Type*} {v : ι → M}
    (hv : LinearIndependent R v) : LinearIndependent Rₛ (f ∘ v) := by
  rw [linearIndependent_iff'ₛ] at hv ⊢
  intro t g₁ g₂ eq i hi
  choose! a fg hfg using IsLocalization.exist_integer_multiples S (t.disjSum t) (Sum.elim g₁ g₂)
  simp_rw [Sum.forall, Finset.inl_mem_disjSum, Sum.elim_inl, Finset.inr_mem_disjSum, Sum.elim_inr,
    Subtype.forall'] at hfg
  apply_fun ((a : R) • ·) at eq
  simp_rw [← t.sum_coe_sort, Finset.smul_sum, ← smul_assoc, ← hfg,
    algebraMap_smul, Function.comp_def, ← map_smul, ← map_sum,
    t.sum_coe_sort (f := fun x ↦ fg (Sum.inl x) • v x),
    t.sum_coe_sort (f := fun x ↦ fg (Sum.inr x) • v x)] at eq
  have ⟨s, eq⟩ := IsLocalizedModule.exists_of_eq (S := S) eq
  simp_rw [Finset.smul_sum, Submonoid.smul_def, smul_smul] at eq
  have := congr(algebraMap R Rₛ $(hv t _ _ eq i hi))
  simpa only [map_mul, (IsLocalization.map_units Rₛ s).mul_right_inj, hfg.1 ⟨i, hi⟩, hfg.2 ⟨i, hi⟩,
    Algebra.smul_def, (IsLocalization.map_units Rₛ a).mul_right_inj] using this

theorem LinearIndependent.of_isLocalizedModule_of_isRegular {ι : Type*} {v : ι → M}
    (hv : LinearIndependent R v) (h : ∀ s : S, IsRegular (s : R)) : LinearIndependent R (f ∘ v) :=
  hv.map_injOn _ <| by
    rw [← Finsupp.range_linearCombination]
    rintro _ ⟨_, r, rfl⟩ _ ⟨_, r', rfl⟩ eq
    congr; ext i
    have ⟨s, eq⟩ := IsLocalizedModule.exists_of_eq (S := S) eq
    simp_rw [Submonoid.smul_def, ← map_smul] at eq
    exact (h s).1 (DFunLike.congr_fun (hv eq) i)

theorem LinearIndependent.localization [Module Rₛ M] [IsScalarTower R Rₛ M]
    {ι : Type*} {b : ι → M} (hli : LinearIndependent R b) :
    LinearIndependent Rₛ b := by
  have := isLocalizedModule_id S M Rₛ
  exact hli.of_isLocalizedModule Rₛ S .id

include f in

lemma IsLocalizedModule.linearIndependent_lift {ι} {v : ι → Mₛ} (hf : LinearIndependent R v) :
    ∃ w : ι → M, LinearIndependent R w := by
  cases isEmpty_or_nonempty ι
  · exact ⟨isEmptyElim, linearIndependent_empty_type⟩
  have inj := hf.smul_left_injective (Classical.arbitrary ι)
  choose sec hsec using surj S f
  use fun i ↦ (sec (v i)).1
  rw [linearIndependent_iff'ₛ] at hf ⊢
  intro t g g' eq i hit
  refine (isRegular_of_smul_left_injective f inj (sec (v i)).2).2 <|
    hf t (fun i ↦ _ * (sec (v i)).2) (fun i ↦ _ * (sec (v i)).2) ?_ i hit
  simp_rw [mul_smul, ← Submonoid.smul_def, hsec, ← map_smul, ← map_sum, eq]

namespace Module.Basis

variable {ι : Type*} (b : Basis ι R M)

noncomputable def ofIsLocalizedModule : Basis ι Rₛ Mₛ :=
  .mk (b.linearIndependent.of_isLocalizedModule Rₛ S f) <| by
    rw [Set.range_comp, span_eq_top_of_isLocalizedModule Rₛ S _ b.span_eq]
