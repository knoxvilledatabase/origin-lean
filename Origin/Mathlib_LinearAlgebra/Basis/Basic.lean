/-
Extracted from LinearAlgebra/Basis/Basic.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Basic results on bases

The main goal of this file is to show the equivalence between bases and families of vectors that are
linearly independent and whose span is the whole space.

There are also various lemmas on bases on specific spaces (such as empty or singletons).

## Main results

* `Basis.linearIndependent`: the basis vectors are linear independent.
* `Basis.span_eq`: the basis vectors span the whole space.
* `Basis.mk`: construct a basis out of `v : ι → M` such that `LinearIndependent v` and
  `span (range v) = ⊤`.
-/

assert_not_exists Ordinal

noncomputable section

universe u

open Function Set Submodule Finsupp

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {M : Type*} {M' : Type*}

namespace Module.Basis

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
  (b : Basis ι R M)

section Properties

theorem repr_range : LinearMap.range (b.repr : M →ₗ[R] ι →₀ R) = Finsupp.supported R R univ := by
  rw [LinearEquiv.range, Finsupp.supported_univ]

theorem mem_span_repr_support (m : M) : m ∈ span R (b '' (b.repr m).support) :=
  (Finsupp.mem_span_image_iff_linearCombination _).2
    ⟨b.repr m, by simp [Finsupp.mem_supported_support]⟩

theorem repr_support_subset_of_mem_span (s : Set ι) {m : M}
    (hm : m ∈ span R (b '' s)) : ↑(b.repr m).support ⊆ s := by
  rcases (Finsupp.mem_span_image_iff_linearCombination _).1 hm with ⟨l, hl, rfl⟩
  rwa [repr_linearCombination, ← Finsupp.mem_supported R l]

theorem mem_span_image {m : M} {s : Set ι} : m ∈ span R (b '' s) ↔ ↑(b.repr m).support ⊆ s :=
  ⟨repr_support_subset_of_mem_span _ _, fun h ↦
    span_mono (Set.image_mono h) (mem_span_repr_support b _)⟩
