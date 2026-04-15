/-
Extracted from Analysis/Normed/Unbundled/InvariantExtension.lean
Genuine: 5 of 6 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# algNormOfAlgEquiv and invariantExtension

Let `K` be a nonarchimedean normed field and `L/K` be a finite algebraic extension. In the comments,
`‖ ⬝ ‖` denotes any power-multiplicative `K`-algebra norm on `L` extending the norm on `K`.

## Main Definitions

* `IsUltrametricDist.algNormOfAlgEquiv` : given `σ : L ≃ₐ[K] L`, the function `L → ℝ` sending
  `x : L` to `‖ σ x ‖` is a `K`-algebra norm on `L`.
* `IsUltrametricDist.invariantExtension` : the function `L → ℝ` sending `x : L` to the maximum of
  `‖ σ x ‖` over all `σ : L ≃ₐ[K] L` is a `K`-algebra norm on `L`.

## Main Results
* `IsUltrametricDist.isPowMul_algNormOfAlgEquiv` : `algNormOfAlgEquiv` is power-multiplicative.
* `IsUltrametricDist.isNonarchimedean_algNormOfAlgEquiv` : `algNormOfAlgEquiv` is nonarchimedean.
* `IsUltrametricDist.algNormOfAlgEquiv_extends` : `algNormOfAlgEquiv` extends the norm on `K`.
* `IsUltrametricDist.isPowMul_invariantExtension` : `invariantExtension` is power-multiplicative.
* `IsUltrametricDist.isNonarchimedean_invariantExtension` : `invariantExtension` is nonarchimedean.
* `IsUltrametricDist.invariantExtension_extends` : `invariantExtension` extends the norm on `K`.

## References
* [S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert]

## Tags

algNormOfAlgEquiv, invariantExtension, norm, nonarchimedean
-/

open scoped NNReal

noncomputable section

variable {K : Type*} [NormedField K] {L : Type*} [Field L] [Algebra K L]
  [h_fin : FiniteDimensional K L] [hu : IsUltrametricDist K]

namespace IsUltrametricDist

section algNormOfAlgEquiv

set_option linter.style.whitespace false in -- manual alignment is not recognised

def algNormOfAlgEquiv (σ : L ≃ₐ[K] L) :
    AlgebraNorm K L where
  toFun x     := Classical.choose (exists_nonarchimedean_pow_mul_seminorm_of_finiteDimensional
    h_fin hu.isNonarchimedean_norm) (σ x)
  map_zero'   := by simp
  add_le' x y := by simp [map_add σ, map_add_le_add]
  neg' x      := by simp [map_neg σ, map_neg_eq_map]
  mul_le' x y := by simp [map_mul σ, map_mul_le_mul]
  smul' x y   := by simp [map_smul σ, map_smul_eq_mul]
  eq_zero_of_map_eq_zero' x hx := EmbeddingLike.map_eq_zero_iff.mp (eq_zero_of_map_eq_zero _ hx)

theorem isPowMul_algNormOfAlgEquiv (σ : L ≃ₐ[K] L) :
    IsPowMul (algNormOfAlgEquiv σ) := by
  intro x n hn
  simp only [algNormOfAlgEquiv_apply, map_pow σ x n]
  exact (Classical.choose_spec (exists_nonarchimedean_pow_mul_seminorm_of_finiteDimensional
    h_fin hu.isNonarchimedean_norm)).1 _ hn

theorem isNonarchimedean_algNormOfAlgEquiv (σ : L ≃ₐ[K] L) :
    IsNonarchimedean (algNormOfAlgEquiv σ) := by
  intro x y
  simp only [algNormOfAlgEquiv_apply, map_add σ]
  exact (Classical.choose_spec (exists_nonarchimedean_pow_mul_seminorm_of_finiteDimensional
    h_fin hu.isNonarchimedean_norm)).2.2 _ _

theorem algNormOfAlgEquiv_extends (σ : L ≃ₐ[K] L) (x : K) :
    (algNormOfAlgEquiv σ) ((algebraMap K L) x) = ‖x‖ := by
  simp only [algNormOfAlgEquiv_apply, AlgEquiv.commutes]
  exact (Classical.choose_spec (exists_nonarchimedean_pow_mul_seminorm_of_finiteDimensional
    h_fin hu.isNonarchimedean_norm)).2.1 _

end algNormOfAlgEquiv

section invariantExtension

variable (K L)

def invariantExtension : AlgebraNorm K L where
  toFun x := iSup fun σ : L ≃ₐ[K] L ↦ algNormOfAlgEquiv σ x
  map_zero' := by simp only [map_zero, ciSup_const]
  add_le' x y := ciSup_le fun σ ↦ le_trans (map_add_le_add (algNormOfAlgEquiv σ) x y)
    (add_le_add (Finite.le_ciSup_of_le σ le_rfl) (Finite.le_ciSup_of_le σ le_rfl))
  neg' x := by simp only [map_neg_eq_map]
  mul_le' x y := ciSup_le fun σ ↦ le_trans (map_mul_le_mul (algNormOfAlgEquiv σ) x y)
    (mul_le_mul (Finite.le_ciSup_of_le σ le_rfl)
      (Finite.le_ciSup_of_le σ le_rfl) (apply_nonneg _ _)
      (Finite.le_ciSup_of_le σ (apply_nonneg _ _)))
  eq_zero_of_map_eq_zero' x := by
    contrapose!
    exact fun hx ↦ ne_of_gt (lt_of_lt_of_le (map_pos_of_ne_zero _ hx)
      (Finite.le_ciSup (fun σ ↦ (algNormOfAlgEquiv σ) x) AlgEquiv.refl))
  smul' r x := by
    simp only [AlgebraNormClass.map_smul_eq_mul,
      Real.mul_iSup_of_nonneg (norm_nonneg _)]
