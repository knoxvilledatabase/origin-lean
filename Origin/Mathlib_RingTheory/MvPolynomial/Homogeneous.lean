/-
Extracted from RingTheory/MvPolynomial/Homogeneous.lean
Genuine: 52 of 59 | Dissolved: 4 | Infrastructure: 3
-/
import Origin.Core
import Mathlib.Algebra.DirectSum.Internal
import Mathlib.Algebra.GradedMonoid
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Algebra.Polynomial.Roots

/-!
# Homogeneous polynomials

A multivariate polynomial `φ` is homogeneous of degree `n`
if all monomials occurring in `φ` have degree `n`.

## Main definitions/lemmas

* `IsHomogeneous φ n`: a predicate that asserts that `φ` is homogeneous of degree `n`.
* `homogeneousSubmodule σ R n`: the submodule of homogeneous polynomials of degree `n`.
* `homogeneousComponent n`: the additive morphism that projects polynomials onto
  their summand that is homogeneous of degree `n`.
* `sum_homogeneousComponent`: every polynomial is the sum of its homogeneous components.

-/

namespace MvPolynomial

variable {σ : Type*} {τ : Type*} {R : Type*} {S : Type*}

open Finsupp

def IsHomogeneous [CommSemiring R] (φ : MvPolynomial σ R) (n : ℕ) :=
  IsWeightedHomogeneous 1 φ n

variable [CommSemiring R]

theorem weightedTotalDegree_one (φ : MvPolynomial σ R) :
    weightedTotalDegree (1 : σ → ℕ) φ = φ.totalDegree := by
  simp only [totalDegree, weightedTotalDegree, weight, LinearMap.toAddMonoidHom_coe,
    linearCombination, Pi.one_apply, Finsupp.coe_lsum, LinearMap.coe_smulRight, LinearMap.id_coe,
    id, Algebra.id.smul_eq_mul, mul_one]

variable (σ R)

def homogeneousSubmodule (n : ℕ) : Submodule R (MvPolynomial σ R) where
  carrier := { x | x.IsHomogeneous n }
  smul_mem' r a ha c hc := by
    rw [coeff_smul] at hc
    apply ha
    intro h
    apply hc
    rw [h]
    exact smul_zero r
  zero_mem' _ hd := False.elim (hd <| coeff_zero _)
  add_mem' {a b} ha hb c hc := by
    rw [coeff_add] at hc
    obtain h | h : coeff c a ≠ 0 ∨ coeff c b ≠ 0 := by
      contrapose! hc
      simp only [hc, add_zero]
    · exact ha h
    · exact hb h

@[simp]
lemma weightedHomogeneousSubmodule_one (n : ℕ) :
    weightedHomogeneousSubmodule R 1 n = homogeneousSubmodule σ R n := rfl

variable {σ R}

@[simp]
theorem mem_homogeneousSubmodule (n : ℕ) (p : MvPolynomial σ R) :
    p ∈ homogeneousSubmodule σ R n ↔ p.IsHomogeneous n := Iff.rfl

variable (σ R)

theorem homogeneousSubmodule_eq_finsupp_supported (n : ℕ) :
    homogeneousSubmodule σ R n = Finsupp.supported _ R { d | d.degree = n } := by
  simp_rw [degree_eq_weight_one]
  exact weightedHomogeneousSubmodule_eq_finsupp_supported R 1 n

variable {σ R}

theorem homogeneousSubmodule_mul (m n : ℕ) :
    homogeneousSubmodule σ R m * homogeneousSubmodule σ R n ≤ homogeneousSubmodule σ R (m + n) :=
  weightedHomogeneousSubmodule_mul 1 m n

section

theorem isHomogeneous_monomial {d : σ →₀ ℕ} (r : R) {n : ℕ} (hn : d.degree = n) :
    IsHomogeneous (monomial d r) n := by
  rw [degree_eq_weight_one] at hn
  exact isWeightedHomogeneous_monomial 1 d r hn

variable (σ)

theorem totalDegree_eq_zero_iff (p : MvPolynomial σ R) :
    p.totalDegree = 0 ↔ ∀ (m : σ →₀ ℕ) (_ : m ∈ p.support) (x : σ), m x = 0 := by
  rw [← weightedTotalDegree_one, weightedTotalDegree_eq_zero_iff _ p]
  exact nonTorsionWeight_of (Function.const σ one_ne_zero)

theorem totalDegree_zero_iff_isHomogeneous {p : MvPolynomial σ R} :
    p.totalDegree = 0 ↔ IsHomogeneous p 0 := by
  rw [← weightedTotalDegree_one,
    ← isWeightedHomogeneous_zero_iff_weightedTotalDegree_eq_zero, IsHomogeneous]

alias ⟨isHomogeneous_of_totalDegree_zero, _⟩ := totalDegree_zero_iff_isHomogeneous

theorem isHomogeneous_C (r : R) : IsHomogeneous (C r : MvPolynomial σ R) 0 := by
  apply isHomogeneous_monomial
  simp only [Finsupp.degree, Finsupp.zero_apply, Finset.sum_const_zero]

variable (R)

theorem isHomogeneous_zero (n : ℕ) : IsHomogeneous (0 : MvPolynomial σ R) n :=
  (homogeneousSubmodule σ R n).zero_mem

theorem isHomogeneous_one : IsHomogeneous (1 : MvPolynomial σ R) 0 :=
  isHomogeneous_C _ _

variable {σ}

theorem isHomogeneous_X (i : σ) : IsHomogeneous (X i : MvPolynomial σ R) 1 := by
  apply isHomogeneous_monomial
  rw [Finsupp.degree, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton]
  exact Finsupp.single_eq_same

end

namespace IsHomogeneous

variable [CommSemiring S] {φ ψ : MvPolynomial σ R} {m n : ℕ}

theorem coeff_eq_zero (hφ : IsHomogeneous φ n) {d : σ →₀ ℕ} (hd : d.degree ≠ n) :
    coeff d φ = 0 := by
  rw [degree_eq_weight_one] at hd
  exact IsWeightedHomogeneous.coeff_eq_zero hφ d hd

-- DISSOLVED: inj_right

theorem add (hφ : IsHomogeneous φ n) (hψ : IsHomogeneous ψ n) : IsHomogeneous (φ + ψ) n :=
  (homogeneousSubmodule σ R n).add_mem hφ hψ

theorem sum {ι : Type*} (s : Finset ι) (φ : ι → MvPolynomial σ R) (n : ℕ)
    (h : ∀ i ∈ s, IsHomogeneous (φ i) n) : IsHomogeneous (∑ i ∈ s, φ i) n :=
  (homogeneousSubmodule σ R n).sum_mem h

theorem mul (hφ : IsHomogeneous φ m) (hψ : IsHomogeneous ψ n) : IsHomogeneous (φ * ψ) (m + n) :=
  homogeneousSubmodule_mul m n <| Submodule.mul_mem_mul hφ hψ

theorem prod {ι : Type*} (s : Finset ι) (φ : ι → MvPolynomial σ R) (n : ι → ℕ)
    (h : ∀ i ∈ s, IsHomogeneous (φ i) (n i)) : IsHomogeneous (∏ i ∈ s, φ i) (∑ i ∈ s, n i) := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro
    simp only [isHomogeneous_one, Finset.sum_empty, Finset.prod_empty]
  · intro i s his IH h
    simp only [his, Finset.prod_insert, Finset.sum_insert, not_false_iff]
    apply (h i (Finset.mem_insert_self _ _)).mul (IH _)
    intro j hjs
    exact h j (Finset.mem_insert_of_mem hjs)

lemma C_mul (hφ : φ.IsHomogeneous m) (r : R) :
    (C r * φ).IsHomogeneous m := by
  simpa only [zero_add] using (isHomogeneous_C _ _).mul hφ

lemma _root_.MvPolynomial.isHomogeneous_C_mul_X (r : R) (i : σ) :
    (C r * X i).IsHomogeneous 1 :=
  (isHomogeneous_X _ _).C_mul _

alias _root_.MvPolynomial.C_mul_X := _root_.MvPolynomial.isHomogeneous_C_mul_X

lemma pow (hφ : φ.IsHomogeneous m) (n : ℕ) : (φ ^ n).IsHomogeneous (m * n) := by
  rw [show φ ^ n = ∏ _i ∈ Finset.range n, φ by simp]
  rw [show m * n = ∑ _i ∈ Finset.range n, m by simp [mul_comm]]
  apply IsHomogeneous.prod _ _ _ (fun _ _ ↦ hφ)

lemma _root_.MvPolynomial.isHomogeneous_X_pow (i : σ) (n : ℕ) :
    (X (R := R) i ^ n).IsHomogeneous n := by
  simpa only [one_mul] using (isHomogeneous_X _ _).pow n

lemma _root_.MvPolynomial.isHomogeneous_C_mul_X_pow (r : R) (i : σ) (n : ℕ) :
    (C r * X i ^ n).IsHomogeneous n :=
  (isHomogeneous_X_pow _ _).C_mul _

lemma eval₂ (hφ : φ.IsHomogeneous m) (f : R →+* MvPolynomial τ S) (g : σ → MvPolynomial τ S)
    (hf : ∀ r, (f r).IsHomogeneous 0) (hg : ∀ i, (g i).IsHomogeneous n) :
    (eval₂ f g φ).IsHomogeneous (n * m) := by
  apply IsHomogeneous.sum
  intro i hi
  rw [← zero_add (n * m)]
  apply IsHomogeneous.mul (hf _) _
  convert IsHomogeneous.prod _ _ (fun k ↦ n * i k) _
  · rw [Finsupp.mem_support_iff] at hi
    rw [← Finset.mul_sum, ← hφ hi, weight_apply]
    simp_rw [smul_eq_mul, Finsupp.sum, Pi.one_apply, mul_one]
  · rintro k -
    apply (hg k).pow

lemma map (hφ : φ.IsHomogeneous n) (f : R →+* S) : (map f φ).IsHomogeneous n := by
  simpa only [one_mul] using hφ.eval₂ _ _ (fun r ↦ isHomogeneous_C _ (f r)) (isHomogeneous_X _)

lemma aeval [Algebra R S] (hφ : φ.IsHomogeneous m)
    (g : σ → MvPolynomial τ S) (hg : ∀ i, (g i).IsHomogeneous n) :
    (aeval g φ).IsHomogeneous (n * m) :=
  hφ.eval₂ _ _ (fun _ ↦ isHomogeneous_C _ _) hg

section CommRing

variable {R σ : Type*} [CommRing R] {φ ψ : MvPolynomial σ R} {n : ℕ}

theorem neg (hφ : IsHomogeneous φ n) : IsHomogeneous (-φ) n :=
  (homogeneousSubmodule σ R n).neg_mem hφ

theorem sub (hφ : IsHomogeneous φ n) (hψ : IsHomogeneous ψ n) : IsHomogeneous (φ - ψ) n :=
  (homogeneousSubmodule σ R n).sub_mem hφ hψ

end CommRing

lemma totalDegree_le (hφ : IsHomogeneous φ n) : φ.totalDegree ≤ n := by
  apply Finset.sup_le
  intro d hd
  rw [mem_support_iff] at hd
  simp_rw [Finsupp.sum, ← hφ hd, weight_apply, Pi.one_apply, smul_eq_mul, mul_one, Finsupp.sum,
    le_rfl]

-- DISSOLVED: totalDegree

theorem rename_isHomogeneous {f : σ → τ} (h : φ.IsHomogeneous n) :
    (rename f φ).IsHomogeneous n := by
  rw [← φ.support_sum_monomial_coeff, map_sum]; simp_rw [rename_monomial]
  apply IsHomogeneous.sum _ _ _ fun d hd ↦ isHomogeneous_monomial _ _
  intro d hd
  apply (Finsupp.sum_mapDomain_index_addMonoidHom fun _ ↦ .id ℕ).trans
  convert h (mem_support_iff.mp hd)
  simp only [weight_apply, AddMonoidHom.id_apply, Pi.one_apply, smul_eq_mul, mul_one]

theorem rename_isHomogeneous_iff {f : σ → τ} (hf : f.Injective) :
    (rename f φ).IsHomogeneous n ↔ φ.IsHomogeneous n := by
  refine ⟨fun h d hd ↦ ?_, rename_isHomogeneous⟩
  convert ← @h (d.mapDomain f) _
  · simp only [weight_apply, Pi.one_apply, smul_eq_mul, mul_one]
    exact Finsupp.sum_mapDomain_index_inj (h := fun _ ↦ id) hf
  · rwa [coeff_rename_mapDomain f hf]

lemma finSuccEquiv_coeff_isHomogeneous {N : ℕ} {φ : MvPolynomial (Fin (N+1)) R} {n : ℕ}
    (hφ : φ.IsHomogeneous n) (i j : ℕ) (h : i + j = n) :
    ((finSuccEquiv _ _ φ).coeff i).IsHomogeneous j := by
  intro d hd
  rw [finSuccEquiv_coeff_coeff] at hd
  have h' : (weight 1) (Finsupp.cons i d) = i + j := by
    simpa [Finset.sum_subset_zero_on_sdiff (g := d.cons i)
     (d.cons_support (y := i)) (by simp) (fun _ _ ↦ rfl), ← h] using hφ hd
  simp only [weight_apply, Pi.one_apply, smul_eq_mul, mul_one, Finsupp.sum_cons,
    add_right_inj] at h' ⊢
  exact h'

lemma coeff_isHomogeneous_of_optionEquivLeft_symm
    [hσ : Finite σ] {p : Polynomial (MvPolynomial σ R)}
    (hp : ((optionEquivLeft R σ).symm p).IsHomogeneous n) (i j : ℕ) (h : i + j = n) :
    (p.coeff i).IsHomogeneous j := by
  obtain ⟨k, ⟨e⟩⟩ := Finite.exists_equiv_fin σ
  let e' := e.optionCongr.trans (_root_.finSuccEquiv _).symm
  let F := renameEquiv R e
  let F' := renameEquiv R e'
  let φ := F' ((optionEquivLeft R σ).symm p)
  have hφ : φ.IsHomogeneous n := hp.rename_isHomogeneous
  suffices IsHomogeneous (F (p.coeff i)) j by
    rwa [← (IsHomogeneous.rename_isHomogeneous_iff e.injective)]
  convert hφ.finSuccEquiv_coeff_isHomogeneous i j h using 1
  dsimp only [φ, F', F, renameEquiv_apply]
  rw [finSuccEquiv_rename_finSuccEquiv, AlgEquiv.apply_symm_apply]
  simp

open Polynomial in

private

-- DISSOLVED: exists_eval_ne_zero_of_coeff_finSuccEquiv_ne_zero_aux

section IsDomain

variable {R σ : Type*} [CommRing R] [IsDomain R] {F G : MvPolynomial σ R} {n : ℕ}

open Cardinal Polynomial

private

-- DISSOLVED: exists_eval_ne_zero_of_totalDegree_le_card_aux

lemma eq_zero_of_forall_eval_eq_zero_of_le_card
    (hF : F.IsHomogeneous n) (h : ∀ r : σ → R, eval r F = 0) (hnR : n ≤ #R) :
    F = 0 := by
  contrapose! h
  -- reduce to the case where σ is finite
  obtain ⟨k, f, hf, F, rfl⟩ := exists_fin_rename F
  have hF₀ : F ≠ 0 := by rintro rfl; simp at h
  have hF : F.IsHomogeneous n := by rwa [rename_isHomogeneous_iff hf] at hF
  obtain ⟨r, hr⟩ := exists_eval_ne_zero_of_totalDegree_le_card_aux hF hF₀ hnR
  obtain ⟨r, rfl⟩ := (Function.factorsThrough_iff _).mp <| (hf.factorsThrough r)
  use r
  rwa [eval_rename]

lemma funext_of_le_card (hF : F.IsHomogeneous n) (hG : G.IsHomogeneous n)
    (h : ∀ r : σ → R, eval r F = eval r G) (hnR : n ≤ #R) :
    F = G := by
  rw [← sub_eq_zero]
  apply eq_zero_of_forall_eval_eq_zero_of_le_card (hF.sub hG) _ hnR
  simpa [sub_eq_zero] using h

lemma eq_zero_of_forall_eval_eq_zero [Infinite R] {F : MvPolynomial σ R} {n : ℕ}
    (hF : F.IsHomogeneous n) (h : ∀ r : σ → R, eval r F = 0) : F = 0 := by
  apply eq_zero_of_forall_eval_eq_zero_of_le_card hF h
  exact (Cardinal.nat_lt_aleph0 _).le.trans <| Cardinal.infinite_iff.mp ‹Infinite R›

lemma funext [Infinite R] {F G : MvPolynomial σ R} {n : ℕ}
    (hF : F.IsHomogeneous n) (hG : G.IsHomogeneous n)
    (h : ∀ r : σ → R, eval r F = eval r G) : F = G := by
  apply funext_of_le_card hF hG h
  exact (Cardinal.nat_lt_aleph0 _).le.trans <| Cardinal.infinite_iff.mp ‹Infinite R›

end IsDomain

instance HomogeneousSubmodule.gcommSemiring : SetLike.GradedMonoid (homogeneousSubmodule σ R) where
  one_mem := isHomogeneous_one σ R
  mul_mem _ _ _ _ := IsHomogeneous.mul

end IsHomogeneous

noncomputable section

open Finset

def homogeneousComponent [CommSemiring R] (n : ℕ) : MvPolynomial σ R →ₗ[R] MvPolynomial σ R :=
  weightedHomogeneousComponent 1 n

section HomogeneousComponent

open Finset Finsupp

variable (n : ℕ) (φ ψ : MvPolynomial σ R)

theorem homogeneousComponent_mem  :
    homogeneousComponent n φ ∈ homogeneousSubmodule σ R n :=
  weightedHomogeneousComponent_mem _ φ n

theorem coeff_homogeneousComponent (d : σ →₀ ℕ) :
    coeff d (homogeneousComponent n φ) = if d.degree = n then coeff d φ else 0 := by
  rw [degree_eq_weight_one]
  convert coeff_weightedHomogeneousComponent n φ d

theorem homogeneousComponent_apply :
    homogeneousComponent n φ = ∑ d ∈ φ.support with d.degree = n, monomial d (coeff d φ) := by
  simp_rw [degree_eq_weight_one]
  convert weightedHomogeneousComponent_apply n φ

theorem homogeneousComponent_isHomogeneous : (homogeneousComponent n φ).IsHomogeneous n :=
  weightedHomogeneousComponent_isWeightedHomogeneous n φ

@[simp]
theorem homogeneousComponent_zero : homogeneousComponent 0 φ = C (coeff 0 φ) :=
  weightedHomogeneousComponent_zero φ (fun _ => Nat.succ_ne_zero Nat.zero)

@[simp]
theorem homogeneousComponent_C_mul (n : ℕ) (r : R) :
    homogeneousComponent n (C r * φ) = C r * homogeneousComponent n φ :=
  weightedHomogeneousComponent_C_mul φ n r

theorem homogeneousComponent_eq_zero'
    (h : ∀ d : σ →₀ ℕ, d ∈ φ.support → d.degree ≠ n) :
    homogeneousComponent n φ = 0 := by
  simp_rw [degree_eq_weight_one] at h
  exact weightedHomogeneousComponent_eq_zero' n φ h

theorem homogeneousComponent_eq_zero (h : φ.totalDegree < n) : homogeneousComponent n φ = 0 := by
  apply homogeneousComponent_eq_zero'
  rw [totalDegree, Finset.sup_lt_iff (lt_of_le_of_lt (Nat.zero_le _) h)] at h
  intro d hd; exact ne_of_lt (h d hd)

theorem sum_homogeneousComponent :
    (∑ i ∈ range (φ.totalDegree + 1), homogeneousComponent i φ) = φ := by
  ext1 d
  suffices φ.totalDegree < d.support.sum d → 0 = coeff d φ by
    simpa [coeff_sum, coeff_homogeneousComponent]
  exact fun h => (coeff_eq_zero_of_totalDegree_lt h).symm

theorem homogeneousComponent_of_mem {m n : ℕ} {p : MvPolynomial σ R}
    (h : p ∈ homogeneousSubmodule σ R n) :
    homogeneousComponent m p = if m = n then p else 0 :=
  weightedHomogeneousComponent_of_mem h

end HomogeneousComponent

end

noncomputable section GradedAlgebra

lemma HomogeneousSubmodule.gradedMonoid :
    SetLike.GradedMonoid (homogeneousSubmodule σ R) :=
  WeightedHomogeneousSubmodule.gradedMonoid

abbrev decomposition :
    DirectSum.Decomposition (homogeneousSubmodule σ R) :=
  weightedDecomposition R (1 : σ → ℕ)

abbrev gradedAlgebra : GradedAlgebra (homogeneousSubmodule σ R) :=
  weightedGradedAlgebra R (1 : σ → ℕ)

theorem decomposition.decompose'_apply (φ : MvPolynomial σ R) (i : ℕ) :
    (decomposition.decompose' φ i : MvPolynomial σ R) = homogeneousComponent i φ :=
  weightedDecomposition.decompose'_apply R _ φ i

theorem decomposition.decompose'_eq :
    decomposition.decompose' = fun φ : MvPolynomial σ R =>
      DirectSum.mk (fun i : ℕ => ↥(homogeneousSubmodule σ R i)) (φ.support.image Finsupp.degree)
        fun m => ⟨homogeneousComponent m φ, homogeneousComponent_mem m φ⟩ := by
  rw [degree_eq_weight_one]
  rfl

end GradedAlgebra

end MvPolynomial
