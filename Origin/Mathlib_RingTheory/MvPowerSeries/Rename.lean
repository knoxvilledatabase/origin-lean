/-
Extracted from RingTheory/MvPowerSeries/Rename.lean
Genuine: 6 of 7 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Renaming variables of power series

This file establishes the `rename` operation on multivariate power series
under a map with finite fibers, which modifies the set of variables.

Unlike polynomials, renaming variables in power series requires a finiteness condition
on the map `f : σ → τ` between the index types. Specifically, we require that `f` has
finite fibers, which is formalized as `Filter.TendstoCofinite f`.
To see why this is necessary, consider a map from infinitely many variables to a single
variable sending each `X_i` to `X`. The sum `X_0 + X_1 + ⋯` is a valid power series in
`ℤ⟦X_0, X_1, ...⟧`, but we cannot rename each `X_i` to `X` since its image `X + X + ⋯`
would have an infinite coefficient for `X`.

To avoid writing this assumption everywhere, we usually work with the typeclass assumption
`Filter.TendstoCofinite f`. Note that this holds automatically if `f` is injective
or if `σ` is finite.

This file is patterned after `Mathlib/Algebra/MvPolynomial/Rename.lean`.

## Main declarations

* `MvPowerSeries.rename`
* `MvPowerSeries.renameEquiv`
* `MvPowerSeries.killCompl`

## TODO

* Show that under appropriate substitution, `MvPowerSeries.substAlgHom` coincides with
  `MvPowerSeries.rename` in the `CommRing` case.

-/

noncomputable section

open Finsupp Filter

variable {σ τ γ R S : Type*} (f : σ → τ) (g : τ → γ) [TendstoCofinite f]

namespace MvPowerSeries

section Semiring

variable [Semiring R] [Semiring S]

def renameFun [TendstoCofinite f] : MvPowerSeries σ R → MvPowerSeries τ R :=
  TendstoCofinite.mapDomain (Finsupp.mapDomain f)

private lemma renameFun_monomial (x : σ →₀ ℕ) (r : R) :
    renameFun f (monomial x r) = monomial (mapDomain f x) r := by
  classical
  ext; simp [coeff_renameFun, coeff_monomial, eq_comm]

private theorem renameFunAux [DecidableEq σ] (x : τ →₀ ℕ) :
    {p : (σ →₀ ℕ) × (σ →₀ ℕ) × (σ →₀ ℕ) | (p.1).mapDomain f = x ∧
      p.2 ∈ Finset.antidiagonal p.1}.Finite := by
  apply Set.Finite.subset
    (s := ↑((TendstoCofinite.finite_preimage_singleton (Finsupp.mapDomain f) x).toFinset.sup
    (fun y ↦ Finset.product {y} (Finset.antidiagonal y))))
  · exact Finset.finite_toSet ..
  · intro; simp
    grind

private theorem renameFunAux' [DecidableEq τ] (x : τ →₀ ℕ) :
    {p : ((τ →₀ ℕ) × (τ →₀ ℕ)) × (σ →₀ ℕ) × (σ →₀ ℕ) | p.1 ∈ Finset.antidiagonal x
      ∧ p.2 ∈ (TendstoCofinite.finite_preimage_singleton (Finsupp.mapDomain f) p.1.1).toFinset ×ˢ
    (TendstoCofinite.finite_preimage_singleton (Finsupp.mapDomain f) p.1.2).toFinset}.Finite := by
  classical
  apply Set.Finite.subset (s := ↑((Finset.antidiagonal x).sup (fun q ↦ Finset.product {q}
    ((TendstoCofinite.finite_preimage_singleton (Finsupp.mapDomain f) q.1).toFinset ×ˢ
      (TendstoCofinite.finite_preimage_singleton (Finsupp.mapDomain f) q.2).toFinset))))
  · exact Finset.finite_toSet ..
  · intro; simp
    grind

private theorem renameFunAuxImage [DecidableEq σ] [DecidableEq τ] (x : τ →₀ ℕ) :
    (renameFunAux' f x).toFinset.image (fun (_, b) ↦ (b.1 + b.2, b)) =
      (renameFunAux f x).toFinset := by
  ext ⟨_, _, _⟩
  simp; grind [Finsupp.mapDomain_add]

open Finset in

private theorem renameFun_mul (p q : MvPowerSeries σ R) :
    renameFun f (p * q) = renameFun f p * renameFun f q := by
  classical
  ext x
  simp only [coeff_renameFun, coeff_mul, sum_mul_sum, ← sum_product']
  rw [← sum_finset_product' (renameFunAux f x).toFinset _ _ (by simp),
    ← sum_finset_product' (renameFunAux' f x).toFinset _ _ (by simp),
    ← renameFunAuxImage f x, sum_image fun _ ↦ by simp; grind]

end Semiring

section CommSemiring

variable [CommSemiring R] [CommSemiring S]
