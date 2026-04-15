/-
Extracted from RingTheory/MvPolynomial/Symmetric/Defs.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Symmetric Polynomials and Elementary Symmetric Polynomials

This file defines symmetric `MvPolynomial`s and the bases of elementary, complete homogeneous,
power sum, and monomial symmetric `MvPolynomial`s. We also prove some basic facts about them.

## Main declarations

* `MvPolynomial.IsSymmetric`

* `MvPolynomial.symmetricSubalgebra`

* `MvPolynomial.esymm`

* `MvPolynomial.hsymm`

* `MvPolynomial.psum`

* `MvPolynomial.msymm`

## Notation

+ `esymm σ R n` is the `n`th elementary symmetric polynomial in `MvPolynomial σ R`.

+ `hsymm σ R n` is the `n`th complete homogeneous symmetric polynomial in `MvPolynomial σ R`.

+ `psum σ R n` is the degree-`n` power sum in `MvPolynomial σ R`, i.e. the sum of monomials
  `(X i)^n` over `i ∈ σ`.

+ `msymm σ R μ` is the monomial symmetric polynomial whose exponents set are the parts
  of `μ ⊢ n` in `MvPolynomial σ R`.

As in other polynomial files, we typically use the notation:

+ `σ τ : Type*` (indexing the variables)

+ `R S : Type*` `[CommSemiring R]` `[CommSemiring S]` (the coefficients)

+ `r : R` elements of the coefficient ring

+ `i : σ`, with corresponding monomial `X i`, often denoted `X_i` by mathematicians

+ `φ ψ : MvPolynomial σ R`

-/

open Equiv (Perm)

noncomputable section

namespace Multiset

variable {R : Type*} [CommSemiring R]

def esymm (s : Multiset R) (n : ℕ) : R :=
  ((s.powersetCard n).map Multiset.prod).sum

theorem _root_.Finset.esymm_map_val {σ} (f : σ → R) (s : Finset σ) (n : ℕ) :
    (s.val.map f).esymm n = (s.powersetCard n).sum fun t => t.prod f := by
  simp only [esymm, powersetCard_map, ← Finset.map_val_val_powersetCard, map_map]
  simp only [Function.comp_apply, Finset.prod_map_val, Finset.sum_map_val]

lemma pow_smul_esymm {S : Type*} [Monoid S] [DistribMulAction S R] [IsScalarTower S R R]
    [SMulCommClass S R R] (s : S) (n : ℕ) (m : Multiset R) :
    s ^ n • m.esymm n = (m.map (s • ·)).esymm n := by
  rw [esymm, smul_sum, map_map]
  trans ((powersetCard n m).map (fun x : Multiset R ↦ s ^ card x • x.prod)).sum
  · refine congr_arg _ (map_congr rfl (fun x hx ↦ ?_))
    rw [Function.comp_apply, (mem_powersetCard.1 hx).2]
  · simp_rw [smul_prod, esymm, powersetCard_map, map_map, Function.comp_def]
