/-
Extracted from Algebra/Polynomial/BigOperators.lean
Genuine: 26 of 32 | Dissolved: 6 | Infrastructure: 0
-/
import Origin.Core

/-!
# Lemmas for the interaction between polynomials and `∑` and `∏`.

Recall that `∑` and `∏` are notation for `Finset.sum` and `Finset.prod` respectively.

## Main results

- `Polynomial.natDegree_prod_of_monic` : the degree of a product of monic polynomials is the
  product of degrees. We prove this only for `[CommSemiring R]`,
  but it ought to be true for `[Semiring R]` and `List.prod`.
- `Polynomial.natDegree_prod` : for polynomials over an integral domain,
  the degree of the product is the sum of degrees.
- `Polynomial.leadingCoeff_prod` : for polynomials over an integral domain,
  the leading coefficient is the product of leading coefficients.
- `Polynomial.prod_X_sub_C_coeff_card_pred` carries most of the content for computing
  the second coefficient of the characteristic polynomial.
-/

open Finset

open Multiset

open Polynomial

universe u w

variable {R : Type u} {ι : Type w}

namespace Polynomial

variable (s : Finset ι)

section Semiring

variable {S : Type*} [Semiring S]

theorem natDegree_list_sum_le (l : List S[X]) :
    natDegree l.sum ≤ (l.map natDegree).foldr max 0 := by
  apply List.sum_le_foldr_max natDegree
  · simp
  · exact natDegree_add_le

theorem natDegree_multiset_sum_le (l : Multiset S[X]) :
    natDegree l.sum ≤ (l.map natDegree).foldr max 0 :=
  Quotient.inductionOn l (by simpa using natDegree_list_sum_le)

theorem natDegree_sum_le (f : ι → S[X]) :
    natDegree (∑ i ∈ s, f i) ≤ s.fold max 0 (natDegree ∘ f) := by
  simpa using natDegree_multiset_sum_le (s.val.map f)

lemma natDegree_sum_le_of_forall_le {n : ℕ} (f : ι → S[X]) (h : ∀ i ∈ s, natDegree (f i) ≤ n) :
    natDegree (∑ i ∈ s, f i) ≤ n :=
  le_trans (natDegree_sum_le s f) <| (Finset.fold_max_le n).mpr <| by simpa

-- DISSOLVED: leadingCoeff_sum_of_degree_eq

theorem degree_list_sum_le_of_forall_degree_le (l : List S[X])
    (n : WithBot ℕ) (hl : ∀ p ∈ l, degree p ≤ n) :
    degree l.sum ≤ n := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hl
    rcases hl with ⟨hhd, htl⟩
    rw [List.sum_cons]
    exact le_trans (degree_add_le hd tl.sum) (max_le hhd (ih htl))

theorem degree_list_sum_le (l : List S[X]) : degree l.sum ≤ (l.map natDegree).maximum := by
  apply degree_list_sum_le_of_forall_degree_le
  intro p hp
  by_cases h : p = 0
  · subst h
    simp
  · rw [degree_eq_natDegree h]
    apply List.le_maximum_of_mem'
    rw [List.mem_map]
    use p
    simp [hp]

theorem natDegree_list_prod_le (l : List S[X]) : natDegree l.prod ≤ (l.map natDegree).sum :=
  l.apply_prod_le_sum_map _ natDegree_one.le fun _ _ => natDegree_mul_le

theorem degree_list_prod_le (l : List S[X]) : degree l.prod ≤ (l.map degree).sum :=
  l.apply_prod_le_sum_map _ degree_one_le degree_mul_le

theorem coeff_list_prod_of_natDegree_le (l : List S[X]) (n : ℕ) (hl : ∀ p ∈ l, natDegree p ≤ n) :
    coeff (List.prod l) (l.length * n) = (l.map fun p => coeff p n).prod := by
  induction l with
  | nil => simp
  | cons hd tl IH =>
    have hl' : ∀ p ∈ tl, natDegree p ≤ n := fun p hp => hl p (List.mem_cons_of_mem _ hp)
    simp only [List.prod_cons, List.map, List.length]
    rw [add_mul, one_mul, add_comm, ← IH hl', mul_comm tl.length]
    have h : natDegree tl.prod ≤ n * tl.length := by
      refine (natDegree_list_prod_le _).trans ?_
      rw [← tl.length_map natDegree, mul_comm]
      refine List.sum_le_card_nsmul _ _ ?_
      simpa using hl'
    exact coeff_mul_add_eq_of_natDegree_le (hl _ List.mem_cons_self) h

end Semiring

section CommSemiring

variable [CommSemiring R] (f : ι → R[X]) (t : Multiset R[X])

theorem natDegree_multiset_prod_le : t.prod.natDegree ≤ (t.map natDegree).sum :=
  Quotient.inductionOn t (by simpa using natDegree_list_prod_le)

theorem natDegree_prod_le : (∏ i ∈ s, f i).natDegree ≤ ∑ i ∈ s, (f i).natDegree := by
  simpa using natDegree_multiset_prod_le (s.1.map f)

theorem degree_multiset_prod_le : t.prod.degree ≤ (t.map Polynomial.degree).sum :=
  Quotient.inductionOn t (by simpa using degree_list_prod_le)

theorem degree_prod_le : (∏ i ∈ s, f i).degree ≤ ∑ i ∈ s, (f i).degree := by
  simpa only [Multiset.map_map] using degree_multiset_prod_le (s.1.map f)

-- DISSOLVED: leadingCoeff_multiset_prod'

-- DISSOLVED: leadingCoeff_prod'

-- DISSOLVED: natDegree_multiset_prod'

-- DISSOLVED: natDegree_prod'

theorem natDegree_multiset_prod_of_monic (h : ∀ f ∈ t, Monic f) :
    t.prod.natDegree = (t.map natDegree).sum := by
  nontriviality R
  apply natDegree_multiset_prod'
  simp_all

theorem degree_multiset_prod_of_monic [Nontrivial R] (h : ∀ f ∈ t, Monic f) :
    t.prod.degree = (t.map degree).sum := by
  have : t.prod ≠ 0 := Monic.ne_zero <| by simpa using monic_multiset_prod_of_monic _ _ h
  rw [degree_eq_natDegree this, natDegree_multiset_prod_of_monic _ h, Nat.cast_multiset_sum,
    Multiset.map_map, Function.comp_def,
    Multiset.map_congr rfl (fun f hf => (degree_eq_natDegree (h f hf).ne_zero).symm)]

theorem natDegree_prod_of_monic (h : ∀ i ∈ s, (f i).Monic) :
    (∏ i ∈ s, f i).natDegree = ∑ i ∈ s, (f i).natDegree := by
  simpa using natDegree_multiset_prod_of_monic (s.1.map f) (by simpa using h)

theorem degree_prod_of_monic [Nontrivial R] (h : ∀ i ∈ s, (f i).Monic) :
    (∏ i ∈ s, f i).degree = ∑ i ∈ s, (f i).degree := by
  simpa using degree_multiset_prod_of_monic (s.1.map f) (by simpa using h)

theorem coeff_multiset_prod_of_natDegree_le (n : ℕ) (hl : ∀ p ∈ t, natDegree p ≤ n) :
    coeff t.prod ((Multiset.card t) * n) = (t.map fun p => coeff p n).prod := by
  induction t using Quotient.inductionOn
  simpa using coeff_list_prod_of_natDegree_le _ _ hl

theorem coeff_prod_of_natDegree_le (f : ι → R[X]) (n : ℕ) (h : ∀ p ∈ s, natDegree (f p) ≤ n) :
    coeff (∏ i ∈ s, f i) (#s * n) = ∏ i ∈ s, coeff (f i) n := by
  obtain ⟨l, hl⟩ := s
  convert coeff_multiset_prod_of_natDegree_le (l.map f) n ?_
  · simp
  · simp
  · simpa using h

-- DISSOLVED: coeff_zero_multiset_prod

theorem coeff_zero_prod : (∏ i ∈ s, f i).coeff 0 = ∏ i ∈ s, (f i).coeff 0 := by
  simpa using coeff_zero_multiset_prod (s.1.map f)

end CommSemiring

section CommRing

variable [CommRing R]

open Monic

theorem multiset_prod_X_sub_C_nextCoeff (t : Multiset R) :
    nextCoeff (t.map fun x => X - C x).prod = -t.sum := by
  rw [nextCoeff_multiset_prod]
  · simp only [nextCoeff_X_sub_C]
    exact t.sum_hom (-AddMonoidHom.id R)
  · intros
    apply monic_X_sub_C

theorem prod_X_sub_C_nextCoeff {s : Finset ι} (f : ι → R) :
    nextCoeff (∏ i ∈ s, (X - C (f i))) = -∑ i ∈ s, f i := by
  simpa using multiset_prod_X_sub_C_nextCoeff (s.1.map f)

theorem multiset_prod_X_sub_C_coeff_card_pred (t : Multiset R) (ht : 0 < Multiset.card t) :
    (t.map fun x => X - C x).prod.coeff ((Multiset.card t) - 1) = -t.sum := by
  nontriviality R
  convert multiset_prod_X_sub_C_nextCoeff (by assumption)
  rw [nextCoeff, if_neg]
  swap
  · rw [natDegree_multiset_prod_of_monic]
    swap
    · simp only [Multiset.mem_map]
      rintro _ ⟨_, _, rfl⟩
      apply monic_X_sub_C
    simp_rw [Multiset.sum_eq_zero_iff, Multiset.mem_map]
    obtain ⟨x, hx⟩ := card_pos_iff_exists_mem.mp ht
    exact fun h => one_ne_zero <| h 1 ⟨_, ⟨x, hx, rfl⟩, natDegree_X_sub_C _⟩
  congr; rw [natDegree_multiset_prod_of_monic] <;> · simp [monic_X_sub_C]

theorem prod_X_sub_C_coeff_card_pred (s : Finset ι) (f : ι → R) (hs : 0 < #s) :
    (∏ i ∈ s, (X - C (f i))).coeff (#s - 1) = -∑ i ∈ s, f i := by
  simpa using multiset_prod_X_sub_C_coeff_card_pred (s.1.map f) (by simpa using hs)

lemma degree_sum_eq_of_linearIndepOn {A : Type*} [CommRing A] [Algebra R A] {f : ι → R[X]}
    {v : ι → A} (h : LinearIndepOn R v s) :
    (∑ i ∈ s, v i • (f i).map (algebraMap R A)).degree = s.sup (fun i ↦ (f i).degree) := by
  apply le_antisymm
  · exact (degree_sum_le s _).trans <| Finset.sup_le fun i hi ↦ (degree_smul_le _ _).trans <|
      degree_map_le.trans <| Finset.le_sup (f := fun i ↦ (f i).degree) hi
  · apply Finset.sup_le
    intro i hi
    by_cases hf : f i = 0
    · simp [hf]
    rw [degree_eq_natDegree hf]
    apply le_degree_of_ne_zero
    rw [finset_sum_coeff]
    conv in (fun _ ↦ _) =>
      ext
      rw [coeff_smul, smul_eq_mul, coeff_map, mul_comm, ← Algebra.smul_def]
    intro H
    exact hf (leadingCoeff_eq_zero.mp (linearIndepOn_finset_iff.mp h _ H i hi))

lemma natDegree_sum_eq_of_linearIndepOn {A : Type*} [CommRing A] [Algebra R A] {f : ι → R[X]}
    {v : ι → A} (h : LinearIndepOn R v s) :
    (∑ i ∈ s, v i • (f i).map (algebraMap R A)).natDegree = s.sup (fun i ↦ (f i).natDegree) := by
  apply le_antisymm
  · exact natDegree_sum_le_of_forall_le _ _ fun i hi ↦ (natDegree_smul_le _ _).trans <|
      natDegree_map_le.trans <| Finset.le_sup (f := fun i ↦ (f i).natDegree) hi
  · apply Finset.sup_le
    intro i hi
    by_cases hf : f i = 0
    · simp [hf]
    apply le_natDegree_of_ne_zero
    rw [finset_sum_coeff]
    conv in (fun _ ↦ _) =>
      ext
      rw [coeff_smul, smul_eq_mul, coeff_map, mul_comm, ← Algebra.smul_def]
    intro H
    exact hf (leadingCoeff_eq_zero.mp (linearIndepOn_finset_iff.mp h _ H i hi))

variable [Nontrivial R]
