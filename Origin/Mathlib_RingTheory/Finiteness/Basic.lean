/-
Extracted from RingTheory/Finiteness/Basic.lean
Genuine: 9 of 11 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Basic results on finitely generated (sub)modules

This file contains the basic results on `Submodule.FG` and `Module.Finite` that do not need heavy
further imports.
-/

assert_not_exists Module.Basis Ideal.radical Matrix Subalgebra

open Function (Surjective)

namespace Submodule

variable {R : Type*} {M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

open Set

theorem fg_bot : (⊥ : Submodule R M).FG :=
  ⟨∅, by rw [Finset.coe_empty, span_empty]⟩

theorem fg_span {s : Set M} (hs : s.Finite) : FG (span R s) :=
  ⟨hs.toFinset, by rw [hs.coe_toFinset]⟩

theorem fg_span_singleton (x : M) : FG (R ∙ x) :=
  fg_span (finite_singleton x)

theorem FG.sup {N₁ N₂ : Submodule R M} (hN₁ : N₁.FG) (hN₂ : N₂.FG) : (N₁ ⊔ N₂).FG :=
  let ⟨t₁, ht₁, span_t₁⟩ := fg_def.mp hN₁
  let ⟨t₂, ht₂, span_t₂⟩ := fg_def.mp hN₂
  fg_def.mpr ⟨t₁ ∪ t₂, ht₁.union ht₂, by rw [span_union, span_t₁, span_t₂]⟩

theorem fg_finset_sup {ι : Type*} (s : Finset ι) (N : ι → Submodule R M) (h : ∀ i ∈ s, (N i).FG) :
    (s.sup N).FG :=
  Finset.sup_induction fg_bot (fun _ ha _ hb => ha.sup hb) h

theorem fg_biSup {ι : Type*} (s : Finset ι) (N : ι → Submodule R M) (h : ∀ i ∈ s, (N i).FG) :
    (⨆ i ∈ s, N i).FG := by simpa only [Finset.sup_eq_iSup] using fg_finset_sup s N h

theorem fg_iSup {ι : Sort*} [Finite ι] (N : ι → Submodule R M) (h : ∀ i, (N i).FG) :
    (iSup N).FG := by
  cases nonempty_fintype (PLift ι)
  simpa [iSup_plift_down] using fg_biSup Finset.univ (N ∘ PLift.down) fun i _ => h i.down

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

variable {S P : Type*} [Semiring S] [AddCommMonoid P] [Module S P]

variable {σ : R →+* S} [RingHomSurjective σ] (f : M →ₛₗ[σ] P)

theorem fg_pi {ι : Type*} {M : ι → Type*} [Finite ι] [∀ i, AddCommMonoid (M i)]
    [∀ i, Module R (M i)] {p : ∀ i, Submodule R (M i)} (hsb : ∀ i, (p i).FG) :
    (pi Set.univ p).FG := by
  classical
    simp_rw [fg_def] at hsb ⊢
    choose t htf hts using hsb
    refine
      ⟨⋃ i, (LinearMap.single R _ i) '' t i, Set.finite_iUnion fun i => (htf i).image _, ?_⟩
    -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 changed `span_image` into `span_image _`
    simp_rw [span_iUnion, span_image _, hts, iSup_map_single]

theorem FG.map {N : Submodule R M} (hs : N.FG) : (N.map f).FG :=
  let ⟨t, ht, span_t⟩ := fg_def.mp hs
  fg_def.mpr ⟨f '' t, ht.image _, by rw [span_image, span_t]⟩
