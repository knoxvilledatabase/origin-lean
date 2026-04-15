/-
Extracted from Analysis/InnerProductSpace/SingularValues.lean
Genuine: 12 of 13 | Dissolved: 1 | Infrastructure: 0
-/
import Origin.Core

/-!
# Singular values for finite-dimensional linear maps

For a linear map `T` between finite-dimensional inner product spaces `E` and `F`, we define the
singular values, which are the square roots of the eigenvalues of `T.adjoint ∘ₗ T`, arranged in
descending order and repeated according to their multiplicity.

With our definition, there are countably infinitely many singular values, but only the first rank(T)
singular values are nonzero.

The singular values are zero-indexed, so `T.singularValues 0` is the first singular value.
This means the positive singular values occur at `0 ≤ i < rank(T)` and not `1 ≤ i ≤ rank(T)`.

## Main definition

- `LinearMap.singularValues`: The infinite but finitely supported sequence of the singular values of
  a linear map.

## Main statements

- `LinearMap.support_singularValues`: The first rank(T) many singular values are positive, and the
  rest are zero.

## Implementation notes

Suppose `T : E →ₗ[𝕜] F` where `dim(E) = n`, `dim(F) = m`.
In mathematical literature, the number of singular values varies, with popular choices including
- `rank(T)` singular values, all of which are positive.
- `min(n,m)` singular values, some of which might be zero.
- `n` singular values, some of which might be zero. This is the approach taken in [axler2024].
- Countably infinitely many singular values, with all but finitely many of them being zero.

We take the last approach for the following reasons:
- It avoid unnecessary dependent typing.
- You can easily convert this definition to the other three by composing with `Fin.val`, but
  converting between any two of the other definitions is more inconvenient because it involves
  multiple `Fin` types.
- If you prefer a definition where there are `k` singular values, you can treat the singular values
  after `k` as junk values.
  Not having to prove that `i < k` when getting the `i`th singular value has similar advantages to
  not having to prove that `y ≠ 0` when calculating `x / y`.
- This API coincides with a potential future API for approximation numbers, which are a
  generalization of singular values to continuous linear maps between possibly-infinite-dimensional
  normed vector spaces.

## TODO

- Generalize singular values to the approximation numbers for maps between
  possibly-infinite-dimensional normed vector spaces.
  This will likely have a similar type signature to the current singular values definition, except
  it will take in a `ContinuousLinearMap` and will not be finitely supported.

## References

* [Sheldon Axler, *Linear Algebra Done Right*][axler2024]

## Tags

singular values
-/

open Module InnerProductSpace

namespace LinearMap

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  (T : E →ₗ[𝕜] F)

noncomputable def singularValues : ℕ →₀ ℝ :=
  Finsupp.embDomain Fin.valEmbedding <|
    Finsupp.ofSupportFinite
      (fun i ↦ √(T.isSymmetric_adjoint_comp_self.eigenvalues rfl i))
      (Set.toFinite _)

theorem singularValues_nonneg (i : ℕ) : 0 ≤ T.singularValues i := by
  rw [singularValues, Finsupp.embDomain_apply, Finsupp.ofSupportFinite_coe]
  split_ifs <;> positivity

-- DISSOLVED: singularValues_pos_iff_ne_zero

theorem singularValues_fin {n : ℕ} (hn : finrank 𝕜 E = n) (i : Fin n) :
    T.singularValues i = √(T.isSymmetric_adjoint_comp_self.eigenvalues hn i) := by
  subst hn
  exact Finsupp.embDomain_apply_self _ _ i

theorem singularValues_of_lt {n : ℕ} (hn : finrank 𝕜 E = n) {i : ℕ} (hi : i < n) :
    T.singularValues i = √(T.isSymmetric_adjoint_comp_self.eigenvalues hn ⟨i, hi⟩) :=
  T.singularValues_fin hn ⟨i, hi⟩

theorem singularValues_of_finrank_le {i : ℕ} (hi : finrank 𝕜 E ≤ i) : T.singularValues i = 0 := by
  apply Finsupp.embDomain_notin_range
  simp [hi]

theorem sq_singularValues_fin {n : ℕ} (hn : finrank 𝕜 E = n) (i : Fin n) :
    T.singularValues i ^ 2 = T.isSymmetric_adjoint_comp_self.eigenvalues hn i := by
  simp [T.singularValues_fin hn, T.isPositive_adjoint_comp_self.nonneg_eigenvalues hn i]

theorem sq_singularValues_of_lt {n : ℕ} (hn : finrank 𝕜 E = n) {i : ℕ} (hi : i < n) :
    T.singularValues i ^ 2 = T.isSymmetric_adjoint_comp_self.eigenvalues hn ⟨i, hi⟩ :=
  T.sq_singularValues_fin hn ⟨i, hi⟩

theorem hasEigenvalue_adjoint_comp_self_sq_singularValues {n : ℕ} (hn : n < finrank 𝕜 E) :
    End.HasEigenvalue (adjoint T ∘ₗ T) (T.singularValues n ^ 2) := by
  convert T.isSymmetric_adjoint_comp_self.hasEigenvalue_eigenvalues rfl ⟨n, hn⟩ using 1
  simp [← T.sq_singularValues_fin]

theorem singularValues_antitone : Antitone T.singularValues := by
  intro i j hij
  by_cases! hj : finrank 𝕜 E ≤ j
  · simpa [T.singularValues_of_finrank_le hj] using T.singularValues_nonneg i
  have : (T.singularValues j : ℝ) ^ 2 ≤ (T.singularValues i : ℝ) ^ 2 := by
    rw [T.sq_singularValues_fin rfl ⟨j, hj⟩, T.sq_singularValues_fin rfl ⟨i, hij.trans_lt hj⟩]
    exact T.isSymmetric_adjoint_comp_self.eigenvalues_antitone rfl hij
  exact le_of_sq_le_sq this (T.singularValues_nonneg i)

theorem injective_iff_forall_lt_finrank_singularValues_pos :
    Function.Injective T ↔ ∀ i < finrank 𝕜 E, 0 < T.singularValues i := by
  have := (adjoint T ∘ₗ T).not_hasEigenvalue_zero_tfae.out 4 0
  rw [← adjoint_comp_self_injective_iff, ← coe_comp, ← ker_eq_bot, ← not_iff_not, this.not_left]
  push Not
  constructor
  · intro h
    obtain ⟨i, hi⟩ := T.isSymmetric_adjoint_comp_self.exists_eigenvalues_eq rfl h
    use i, i.isLt
    simp [RCLike.ofReal_eq_zero.mp hi, T.singularValues_fin rfl]
  · intro ⟨i, h, hz⟩
    convert T.isSymmetric_adjoint_comp_self.hasEigenvalue_eigenvalues rfl ⟨i, h⟩
    rw [← sq_singularValues_of_lt, le_antisymm hz (T.singularValues_nonneg i)]
    simp

theorem card_support_singularValues : T.singularValues.support.card = finrank 𝕜 T.range := by
  have hS : ∀ m ∈ T.singularValues.support, m < finrank 𝕜 E := by
    grind [singularValues_of_finrank_le]
  have hT := T.isSymmetric_adjoint_comp_self
  have : T.singularValues.support.attachFin hS = ({i | hT.eigenvalues rfl i = (0 : 𝕜)} : Finset _)ᶜ
    := by ext i; simp [T.singularValues_fin, T.isPositive_adjoint_comp_self.nonneg_eigenvalues]
  rw [← T.singularValues.support.card_attachFin hS, this, Finset.card_compl, Fintype.card_fin,
    hT.card_filter_eigenvalues_eq rfl 0, Module.End.eigenspace_zero,
    ← (T.adjoint ∘ₗ T).finrank_range_add_finrank_ker, add_tsub_cancel_right,
    T.range_adjoint_comp_self, finrank_range_adjoint]

theorem isLowerSet_support_singularValues : IsLowerSet (T.singularValues.support : Set ℕ) := by
  intro a b hl ha
  rw [Finset.mem_coe, Finsupp.mem_support_iff, ← singularValues_pos_iff_ne_zero] at ⊢ ha
  order [T.singularValues_antitone hl]
