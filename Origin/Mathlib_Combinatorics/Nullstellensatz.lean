/-
Extracted from Combinatorics/Nullstellensatz.lean
Genuine: 6 of 7 | Dissolved: 1 | Infrastructure: 0
-/
import Origin.Core

/-! # Alon's Combinatorial Nullstellensatz

This is a formalization of Noga Alon's Combinatorial Nullstellensatz. It follows [Alon_1999].

We consider a family `S : σ → Finset R` of finite subsets of a domain `R`
and a multivariate polynomial `f` in `MvPolynomial σ R`.
The combinatorial Nullstellensatz gives combinatorial constraints for
the vanishing of `f` at any `x : σ → R` such that `x s ∈ S s` for all `s`.

- `MvPolynomial.eq_zero_of_eval_zero_at_prod_finset` :
  if `f` vanishes at any such point and `f.degreeOf s < #(S s)` for all `s`,
  then `f = 0`.

- `combinatorial_nullstellensatz_exists_linearCombination`
  If `f` vanishes at every such point, then it can be written as a linear combination
  `f = linearCombination (MvPolynomial σ R) (fun i ↦ ∏ r ∈ S i, (X i - C r)) h`,
  for some `h : σ →₀ MvPolynomial σ R` such that
  `((∏ r ∈ S s, (X i - C r)) * h i).totalDegree ≤ f.totalDegree` for all `s`.

- `combinatorial_nullstellensatz_exists_eval_nonzero`
  a multi-index `t : σ →₀ ℕ` such that `t s < (S s).card` for all `s`,
  `f.totalDegree = t.degree` and `f.coeff t ≠ 0`,
  there exists a point `x : σ → R` such that `x s ∈ S s` for all `s` and `f.eval s ≠ 0`.

## TODO

- Applications
- relation with Schwartz–Zippel lemma, as in [Rote_2023]

## References

- [Alon, *Combinatorial Nullstellensatz*][Alon_1999]

- [Rote, *The Generalized Combinatorial Lasoń-Alon-Zippel-Schwartz
  Nullstellensatz Lemma*][Rote_2023]

-/

open Finsupp

open scoped Finset

variable {R : Type*} [CommRing R]

namespace MvPolynomial

open Finsupp Function

theorem eq_zero_of_eval_zero_at_prod_finset {σ : Type*} [Finite σ] [IsDomain R]
    (P : MvPolynomial σ R) (S : σ → Finset R)
    (Hdeg : ∀ i, P.degreeOf i < #(S i))
    (Heval : ∀ (x : σ → R), (∀ i, x i ∈ S i) → eval x P = 0) :
    P = 0 := by
  induction σ using Finite.induction_empty_option with
  | @of_equiv σ τ e h =>
    suffices MvPolynomial.rename e.symm P = 0 by
      have that := MvPolynomial.rename_injective (R := R) e.symm (e.symm.injective)
      rw [RingHom.injective_iff_ker_eq_bot] at that
      rwa [← RingHom.mem_ker, that] at this
    apply h _ (fun i ↦ S (e i))
    · intro i
      classical
      convert Hdeg (e i)
      conv_lhs => rw [← e.symm_apply_apply i, degreeOf_rename_of_injective e.symm.injective]
    · intro x hx
      simp only [MvPolynomial.eval_rename]
      apply Heval
      intro s
      simp only [Function.comp_apply]
      convert hx (e.symm s)
      simp only [Equiv.apply_symm_apply]
  | h_empty =>
    suffices P = C (constantCoeff P) by
      specialize Heval default (fun i ↦ PEmpty.elim i)
      rw [this, eval_C] at Heval
      rw [this, Heval, C_0]
    ext m
    suffices m = 0 by simp [this, ← constantCoeff_eq]
    ext d; exact PEmpty.elim d
  | @h_option σ _ h =>
    set Q := optionEquivLeft R σ P with hQ
    suffices Q = 0 by
      rw [← AlgEquiv.symm_apply_apply (optionEquivLeft R σ) P, ← hQ, this, map_zero]
    have Heval' (x : σ → R) (hx : ∀ i, x i ∈ S (some i)) : Polynomial.map (eval x) Q = 0 := by
      apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ (S none)
      · intro y hy
        rw [← optionEquivLeft_elim_eval]
        apply Heval
        simp only [Option.forall, Option.elim_none, hy, Option.elim_some, hx, implies_true,
          and_self]
      · apply lt_of_le_of_lt _ (Hdeg none)
        rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
        intro d hd
        simp only [hQ]
        rw [MvPolynomial.coeff_eval_eq_eval_coeff]
        convert map_zero (MvPolynomial.eval x)
        ext m
        simp only [coeff_zero]
        set n := (embDomain Function.Embedding.some m).update none d with hn
        rw [eq_option_embedding_update_none_iff] at hn
        rw [← hn.1, ← hn.2, optionEquivLeft_coeff_some_coeff_none]
        by_contra hm
        apply not_le.mpr hd
        rw [MvPolynomial.degreeOf_eq_sup]
        rw [← ne_eq, ← MvPolynomial.mem_support_iff] at hm
        convert Finset.le_sup hm
        exact hn.1.symm
    ext m d
    simp only [Polynomial.coeff_zero, coeff_zero]
    suffices Q.coeff m = 0 by simp only [this, coeff_zero]
    apply h _ (fun i ↦ S (some i))
    · intro i
      apply lt_of_le_of_lt _ (Hdeg (some i))
      simp only [degreeOf_eq_sup, Finset.sup_le_iff, mem_support_iff, ne_eq]
      intro e he
      set n := (embDomain Function.Embedding.some e).update none m with hn
      rw [eq_option_embedding_update_none_iff] at hn
      rw [hQ, ← hn.1, ← hn.2, optionEquivLeft_coeff_some_coeff_none, ← ne_eq,
        ← MvPolynomial.mem_support_iff] at he
      convert Finset.le_sup he
      rw [← hn.2, some_apply]
    · intro x hx
      specialize Heval' x hx
      rw [Polynomial.ext_iff] at Heval'
      simpa only [Polynomial.coeff_map, Polynomial.coeff_zero] using Heval' m

open MonomialOrder

variable {σ : Type*}

private noncomputable def Alon.P (S : Finset R) (i : σ) : MvPolynomial σ R :=
  ∏ r ∈ S, (X i - C r)

private theorem Alon.degree_P [Nontrivial R] (m : MonomialOrder σ) (S : Finset R) (i : σ) :
    m.degree (Alon.P S i) = single i #S := by
  simp only [P]
  rw [degree_prod_of_regular]
  · simp [Finset.sum_congr rfl (fun r _ ↦ m.degree_X_sub_C i r)]
  · intro r _
    rw [m.monic_X_sub_C]
    exact isRegular_one

private theorem Alon.monic_P [Nontrivial R] (m : MonomialOrder σ) (S : Finset R) (i : σ) :
    m.Monic (P S i) :=
  Monic.prod (fun r _ ↦ m.monic_X_sub_C i r)

private lemma Alon.of_mem_P_support {ι : Type*} (i : ι) (S : Finset R) (m : ι →₀ ℕ)
    (hm : m ∈ (Alon.P S i).support) :
    ∃ e ≤ S.card, m = single i e := by
  classical
  have hP : Alon.P S i = .rename (fun _ ↦ i) (Alon.P S ()) := by simp [Alon.P, map_prod]
  rw [hP, support_rename_of_injective (Function.injective_of_subsingleton _)] at hm
  simp only [Finset.mem_image, mem_support_iff, ne_eq] at hm
  obtain ⟨e, he, hm⟩ := hm
  haveI : Nontrivial R := nontrivial_of_ne _ _ he
  refine ⟨e (), ?_, ?_⟩
  · suffices e ≼[lex] single () #S by
      simpa [MonomialOrder.lex_le_iff_of_unique] using this
    rw [← Alon.degree_P]
    apply MonomialOrder.le_degree
    rw [mem_support_iff]
    convert he
  · rw [← hm]
    ext j
    by_cases hj : j = i
    · rw [hj, mapDomain_apply (Function.injective_of_subsingleton _), single_eq_same]
    · rw [mapDomain_notin_range, single_eq_of_ne hj]
      simp [Set.range_const, Set.mem_singleton_iff, hj]

variable [Finite σ]

theorem combinatorial_nullstellensatz_exists_linearCombination
    [IsDomain R] (S : σ → Finset R) (Sne : ∀ i, (S i).Nonempty)
    (f : MvPolynomial σ R) (Heval : ∀ (x : σ → R), (∀ i, x i ∈ S i) → eval x f = 0) :
    ∃ (h : σ →₀ MvPolynomial σ R),
      (∀ i, ((∏ s ∈ S i, (X i - C s)) * h i).totalDegree ≤ f.totalDegree) ∧
      f = linearCombination (MvPolynomial σ R) (fun i ↦ ∏ r ∈ S i, (X i - C r)) h := by
  letI : LinearOrder σ := WellOrderingRel.isWellOrder.linearOrder
  obtain ⟨h, r, hf, hh, hr⟩ := degLex.div (b := fun i ↦ Alon.P (S i) i)
      (fun i ↦ by simp only [(Alon.monic_P ..).leadingCoeff_eq_one, isUnit_one]) f
  use h
  suffices r = 0 by
    rw [this, add_zero] at hf
    exact ⟨fun i ↦ degLex_totalDegree_monotone (hh i), hf⟩
  apply eq_zero_of_eval_zero_at_prod_finset r S
  · intro i
    rw [degreeOf_eq_sup, Finset.sup_lt_iff (by simp [Sne i])]
    intro c hc
    rw [← not_le]
    intro h'
    apply hr c hc i
    intro j
    rw [Alon.degree_P, single_apply]
    split_ifs with hj
    · rw [← hj]
      exact h'
    · exact zero_le _
  · intro x hx
    rw [Iff.symm sub_eq_iff_eq_add'] at hf
    rw [← hf, map_sub, Heval x hx, zero_sub, neg_eq_zero,
      linearCombination_apply, map_finsuppSum, Finsupp.sum, Finset.sum_eq_zero]
    intro i _
    rw [smul_eq_mul, map_mul]
    convert mul_zero _
    rw [Alon.P, map_prod]
    apply Finset.prod_eq_zero (hx i)
    simp

-- DISSOLVED: combinatorial_nullstellensatz_exists_eval_nonzero

end MvPolynomial
