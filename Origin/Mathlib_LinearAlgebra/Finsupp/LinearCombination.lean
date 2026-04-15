/-
Extracted from LinearAlgebra/Finsupp/LinearCombination.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# `Finsupp.linearCombination`

## Main definitions

* `Finsupp.linearCombination R (v : ι → M)`: sends `l : ι →₀ R` to the linear combination of
  `v i` with coefficients `l i`;
* `Finsupp.linearCombinationOn`: a restricted version of `Finsupp.linearCombination` with domain

* `Fintype.linearCombination R (v : ι → M)`: sends `l : ι → R` to the linear combination of
  `v i` with coefficients `l i` (for a finite type `ι`)

* `Finsupp.bilinearCombination R S`, `Fintype.bilinearCombination R S`:
  a bilinear version of `Finsupp.linearCombination` and `Fintype.linearCombination`.
  It requires that `M` is both an `R`-module and an `S`-module, with `SMulCommClass R S M`;
  the case `S = R` typically requires that `R` is commutative.

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

section LinearCombination

variable (R)

variable {α' : Type*} {M' : Type*} [AddCommMonoid M'] [Module R M'] (v : α → M) {v' : α' → M'}

def linearCombination : (α →₀ R) →ₗ[R] M :=
  Finsupp.lsum ℕ fun i => LinearMap.id.smulRight (v i)

variable {v}

theorem linearCombination_apply_of_mem_supported {l : α →₀ R} {s : Finset α}
    (hs : l ∈ supported R R (↑s : Set α)) : linearCombination R v l = s.sum fun i => l i • v i :=
  Finset.sum_subset hs fun x _ hxg =>
    show l x • v x = 0 by rw [notMem_support_iff.1 hxg, zero_smul]
