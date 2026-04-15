/-
Extracted from LinearAlgebra/Eigenspace/Basic.lean
Genuine: 9 of 9 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Eigenvectors and eigenvalues

This file defines eigenspaces, eigenvalues, and eigenvectors, as well as their generalized
counterparts. We follow Axler's approach [axler2024] because it allows us to derive many properties
without choosing a basis and without using matrices.

An eigenspace of a linear map `f` for a scalar `μ` is the kernel of the map `(f - μ • id)`. The
nonzero elements of an eigenspace are eigenvectors `x`. They have the property `f x = μ • x`. If
there are eigenvectors for a scalar `μ`, the scalar `μ` is called an eigenvalue.

There is no consensus in the literature whether `0` is an eigenvector. Our definition of
`HasEigenvector` permits only nonzero vectors. For an eigenvector `x` that may also be `0`, we
write `x ∈ f.eigenspace μ`.

A generalized eigenspace of a linear map `f` for a natural number `k` and a scalar `μ` is the kernel
of the map `(f - μ • id) ^ k`. The nonzero elements of a generalized eigenspace are generalized
eigenvectors `x`. If there are generalized eigenvectors for a natural number `k` and a scalar `μ`,
the scalar `μ` is called a generalized eigenvalue.

The fact that the eigenvalues are the roots of the minimal polynomial is proved in
`LinearAlgebra.Eigenspace.Minpoly`.

The existence of eigenvalues over an algebraically closed field
(and the fact that the generalized eigenspaces then span) is deferred to
`LinearAlgebra.Eigenspace.IsAlgClosed`.

## References

* [Sheldon Axler, *Linear Algebra Done Right*][axler2024]
* https://en.wikipedia.org/wiki/Eigenvalues_and_eigenvectors

## Tags

eigenspace, eigenvector, eigenvalue, eigen
-/

universe u v w

namespace Module

namespace End

open Module Set

variable {K R : Type v} {V M : Type w} [CommRing R] [AddCommGroup M] [Module R M] [Field K]
  [AddCommGroup V] [Module K V]

def genEigenspace (f : End R M) (μ : R) : ℕ∞ →o Submodule R M where
  toFun k := ⨆ l : ℕ, ⨆ _ : l ≤ k, LinearMap.ker ((f - μ • 1) ^ l)
  monotone' _ _ hkl := biSup_mono fun _ hi ↦ hi.trans hkl

lemma mem_genEigenspace {f : End R M} {μ : R} {k : ℕ∞} {x : M} :
    x ∈ f.genEigenspace μ k ↔ ∃ l : ℕ, l ≤ k ∧ x ∈ LinearMap.ker ((f - μ • 1) ^ l) := by
  have : Nonempty {l : ℕ // l ≤ k} := ⟨⟨0, zero_le _⟩⟩
  have : Directed (ι := { i : ℕ // i ≤ k }) (· ≤ ·) fun i ↦ LinearMap.ker ((f - μ • 1) ^ (i : ℕ)) :=
    Monotone.directed_le fun m n h ↦ by simpa using (f - μ • 1).iterateKer.monotone h
  simp_rw [genEigenspace, OrderHom.coe_mk, LinearMap.mem_ker, iSup_subtype',
    Submodule.mem_iSup_of_directed _ this, LinearMap.mem_ker, Subtype.exists, exists_prop]

lemma genEigenspace_directed {f : End R M} {μ : R} {k : ℕ∞} :
    Directed (· ≤ ·) (fun l : {l : ℕ // l ≤ k} ↦ f.genEigenspace μ l) := by
  have aux : Monotone ((↑) : {l : ℕ // l ≤ k} → ℕ∞) := fun x y h ↦ by simpa using h
  exact ((genEigenspace f μ).monotone.comp aux).directed_le

lemma mem_genEigenspace_nat {f : End R M} {μ : R} {k : ℕ} {x : M} :
    x ∈ f.genEigenspace μ k ↔ x ∈ LinearMap.ker ((f - μ • 1) ^ k) := by
  rw [mem_genEigenspace]
  constructor
  · rintro ⟨l, hl, hx⟩
    simp only [Nat.cast_le] at hl
    exact (f - μ • 1).iterateKer.monotone hl hx
  · intro hx
    exact ⟨k, le_rfl, hx⟩

lemma mem_genEigenspace_top {f : End R M} {μ : R} {x : M} :
    x ∈ f.genEigenspace μ ⊤ ↔ ∃ k : ℕ, x ∈ LinearMap.ker ((f - μ • 1) ^ k) := by
  simp [mem_genEigenspace]

lemma genEigenspace_nat {f : End R M} {μ : R} {k : ℕ} :
    f.genEigenspace μ k = LinearMap.ker ((f - μ • 1) ^ k) := by
  ext; simp [mem_genEigenspace_nat]

lemma genEigenspace_eq_iSup_genEigenspace_nat (f : End R M) (μ : R) (k : ℕ∞) :
    f.genEigenspace μ k = ⨆ l : {l : ℕ // l ≤ k}, f.genEigenspace μ l := by
  simp_rw [genEigenspace_nat, genEigenspace, OrderHom.coe_mk, iSup_subtype]

lemma genEigenspace_top (f : End R M) (μ : R) :
    f.genEigenspace μ ⊤ = ⨆ k : ℕ, f.genEigenspace μ k := by
  rw [genEigenspace_eq_iSup_genEigenspace_nat, iSup_subtype]
  simp only [le_top, iSup_pos]

lemma genEigenspace_one {f : End R M} {μ : R} :
    f.genEigenspace μ 1 = LinearMap.ker (f - μ • 1) := by
  rw [← Nat.cast_one, genEigenspace_nat, pow_one]
