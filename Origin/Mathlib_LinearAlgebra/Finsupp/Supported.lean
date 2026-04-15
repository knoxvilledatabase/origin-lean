/-
Extracted from LinearAlgebra/Finsupp/Supported.lean
Genuine: 8 of 9 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# `Finsupp`s supported on a given submodule

* `Finsupp.restrictDom`: `Finsupp.filter` as a linear map to `Finsupp.supported s`;
  `Finsupp.supported R R s` and codomain `Submodule.span R (v '' s)`;
* `Finsupp.supportedEquivFinsupp`: a linear equivalence between the functions `α →₀ M` supported
  on `s` and the functions `s →₀ M`;
* `Finsupp.domLCongr`: a `LinearEquiv` version of `Finsupp.domCongr`;
* `Finsupp.congr`: if the sets `s` and `t` are equivalent, then `supported M R s` is equivalent to
  `supported M R t`;

## Tags

function with finite support, module, linear algebra
-/

noncomputable section

open Set LinearMap Submodule

namespace Finsupp

variable {α : Type*} {M : Type*} {N : Type*} {P : Type*} {R : Type*} {S : Type*}

variable [Semiring R] [Semiring S] [AddCommMonoid M] [Module R M]

variable [AddCommMonoid N] [Module R N]

variable [AddCommMonoid P] [Module R P]

variable (M R)

def supported (s : Set α) : Submodule R (α →₀ M) where
  carrier := { p | ↑p.support ⊆ s }
  add_mem' {p q} hp hq := by
    classical
    refine Subset.trans (Subset.trans (Finset.coe_subset.2 support_add) ?_) (union_subset hp hq)
    rw [Finset.coe_union]
  zero_mem' := by
    simp only [subset_def, Finset.mem_coe, Set.mem_setOf_eq, mem_support_iff, zero_apply]
    intro h ha
    exact (ha rfl).elim
  smul_mem' _ _ hp := Subset.trans (Finset.coe_subset.2 support_smul) hp

variable {M}

theorem mem_supported' {s : Set α} (p : α →₀ M) :
    p ∈ supported M R s ↔ ∀ x ∉ s, p x = 0 := by
  simp [mem_supported, Set.subset_def, not_imp_comm]

theorem mem_supported_support (p : α →₀ M) : p ∈ Finsupp.supported M R (p.support : Set α) := by
  rw [Finsupp.mem_supported]

theorem single_mem_supported {s : Set α} {a : α} (b : M) (h : a ∈ s) :
    single a b ∈ supported M R s :=
  Set.Subset.trans support_single_subset (Finset.singleton_subset_set_iff.2 h)

theorem supported_eq_span_single (s : Set α) :
    supported R R s = span R ((fun i => single i 1) '' s) := by
  refine (span_eq_of_le _ ?_ (SetLike.le_def.2 fun l hl => ?_)).symm
  · rintro _ ⟨_, hp, rfl⟩
    exact single_mem_supported R 1 hp
  · rw [← l.sum_single]
    refine sum_mem fun i il => ?_
    rw [show single i (l i) = l i • single i 1 by simp]
    exact smul_mem _ (l i) (subset_span (mem_image_of_mem _ (hl il)))

lemma single_mem_span_single [Nontrivial R] {a : α} {s : Set α} :
    single a 1 ∈ Submodule.span R ((single · (1 : R)) '' s) ↔ a ∈ s := by
  refine ⟨fun h => ?_, fun h => Submodule.subset_span <| Set.mem_image_of_mem _ h⟩
  rw [← Finsupp.supported_eq_span_single, Finsupp.mem_supported,
    Finsupp.support_single_ne_zero _ (one_ne_zero' R)] at h
  simpa using h

theorem span_le_supported_biUnion_support (s : Set (α →₀ M)) :
    span R s ≤ supported M R (⋃ x ∈ s, x.support) :=
  span_le.mpr fun _ h ↦ subset_biUnion_of_mem h (u := (SetLike.coe ·.support))

variable (M)

def restrictDom (s : Set α) [DecidablePred (· ∈ s)] : (α →₀ M) →ₗ[R] supported M R s :=
  LinearMap.codRestrict _
    { toFun := filter (· ∈ s)
      map_add' := fun _ _ => filter_add
      map_smul' := fun _ _ => filter_smul } fun l =>
    (mem_supported' _ _).2 fun _ => filter_apply_neg (· ∈ s) l

variable {M R}
