/-
Extracted from Combinatorics/Schnirelmann.lean
Genuine: 13 of 15 | Dissolved: 2 | Infrastructure: 0
-/
import Origin.Core

/-!
# Schnirelmann density

We define the Schnirelmann density of a set `A` of natural numbers as
$inf_{n > 0} |A ∩ {1,...,n}| / n$. As this density is very sensitive to changes in small values,
we must exclude `0` from the infimum, and from the intersection.

## Main statements

* Simple bounds on the Schnirelmann density, that it is between 0 and 1 are given in
  `schnirelmannDensity_nonneg` and `schnirelmannDensity_le_one`.
* `schnirelmannDensity_le_of_notMem`: If `k ∉ A`, the density can be easily upper-bounded by
  `1 - k⁻¹`

## Implementation notes

Despite the definition being noncomputable, we include a decidable instance argument, since this
makes the definition easier to use in explicit cases.
Further, we use `Finset.Ioc` rather than a set intersection since the set is finite by construction,
which reduces the proof obligations later that would arise with `Nat.card`.

## TODO
* Give other calculations of the density, for example powers and their sumsets.
* Define other densities like the lower and upper asymptotic density, and the natural density,
  and show how these relate to the Schnirelmann density.
* Prove Schnirelmann's theorem and Mann's theorem on the subadditivity of this density.

## References

* [Ruzsa, Imre, *Sumsets and structure*][ruzsa2009]
-/

open Finset

noncomputable def schnirelmannDensity (A : Set ℕ) [DecidablePred (· ∈ A)] : ℝ :=
  ⨅ n : {n : ℕ // 0 < n}, #{a ∈ Ioc 0 n | a ∈ A} / n

variable {A : Set ℕ} [DecidablePred (· ∈ A)]

lemma schnirelmannDensity_nonneg : 0 ≤ schnirelmannDensity A :=
  Real.iInf_nonneg (fun _ => by positivity)

-- DISSOLVED: schnirelmannDensity_le_div

lemma schnirelmannDensity_mul_le_card_filter {n : ℕ} :
    schnirelmannDensity A * n ≤ #{a ∈ Ioc 0 n | a ∈ A} := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  exact (le_div_iff₀ (by positivity)).1 (schnirelmannDensity_le_div hn)

-- DISSOLVED: schnirelmannDensity_le_of_le

lemma schnirelmannDensity_le_one : schnirelmannDensity A ≤ 1 :=
  schnirelmannDensity_le_of_le 1 one_ne_zero <|
    by rw [Nat.cast_one, div_one, Nat.cast_le_one]; exact card_filter_le _ _

lemma schnirelmannDensity_le_of_notMem {k : ℕ} (hk : k ∉ A) :
    schnirelmannDensity A ≤ 1 - (k⁻¹ : ℝ) := by
  rcases k.eq_zero_or_pos with rfl | hk'
  · simpa using schnirelmannDensity_le_one
  apply schnirelmannDensity_le_of_le k hk'.ne'
  rw [← one_div, one_sub_div (Nat.cast_pos.2 hk').ne']
  gcongr
  rw [← Nat.cast_pred hk', Nat.cast_le]
  suffices {a ∈ Ioc 0 k | a ∈ A} ⊆ Ioo 0 k from (card_le_card this).trans_eq (by simp)
  rw [← Ioo_insert_right hk', filter_insert, if_neg hk]
  exact filter_subset _ _

lemma schnirelmannDensity_eq_zero_of_one_notMem (h : 1 ∉ A) : schnirelmannDensity A = 0 :=
  ((schnirelmannDensity_le_of_notMem h).trans (by simp)).antisymm schnirelmannDensity_nonneg

lemma schnirelmannDensity_le_of_subset {B : Set ℕ} [DecidablePred (· ∈ B)] (h : A ⊆ B) :
    schnirelmannDensity A ≤ schnirelmannDensity B :=
  ciInf_mono ⟨0, fun _ ⟨_, hx⟩ ↦ hx ▸ by positivity⟩ fun _ ↦ by gcongr

lemma schnirelmannDensity_eq_one_iff : schnirelmannDensity A = 1 ↔ {0}ᶜ ⊆ A := by
  rw [le_antisymm_iff, and_iff_right schnirelmannDensity_le_one]
  constructor
  · rw [← not_imp_not, not_le]
    simp only [Set.not_subset, forall_exists_index, and_imp]
    intro x hx hx'
    apply (schnirelmannDensity_le_of_notMem hx').trans_lt
    simpa only [one_div, sub_lt_self_iff, inv_pos, Nat.cast_pos, pos_iff_ne_zero] using hx
  · intro h
    refine le_ciInf fun ⟨n, hn⟩ => ?_
    rw [one_le_div (Nat.cast_pos.2 hn), Nat.cast_le, filter_true_of_mem, Nat.card_Ioc, Nat.sub_zero]
    rintro x hx
    exact h (mem_Ioc.1 hx).1.ne'

lemma schnirelmannDensity_eq_one_iff_of_zero_mem (hA : 0 ∈ A) :
    schnirelmannDensity A = 1 ↔ A = Set.univ := by
  rw [schnirelmannDensity_eq_one_iff]
  constructor
  · refine fun h => Set.eq_univ_of_forall fun x => ?_
    rcases eq_or_ne x 0 with rfl | hx
    · exact hA
    · exact h hx
  · rintro rfl
    exact Set.subset_univ {0}ᶜ

lemma le_schnirelmannDensity_iff {x : ℝ} :
    x ≤ schnirelmannDensity A ↔ ∀ n : ℕ, 0 < n → x ≤ #{a ∈ Ioc 0 n | a ∈ A} / n :=
  (le_ciInf_iff ⟨0, fun _ ⟨_, hx⟩ => hx ▸ by positivity⟩).trans Subtype.forall

lemma schnirelmannDensity_lt_iff {x : ℝ} :
    schnirelmannDensity A < x ↔ ∃ n : ℕ, 0 < n ∧ #{a ∈ Ioc 0 n | a ∈ A} / n < x := by
  rw [← not_le, le_schnirelmannDensity_iff]; simp

lemma schnirelmannDensity_le_iff_forall {x : ℝ} :
    schnirelmannDensity A ≤ x ↔
      ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, 0 < n ∧ #{a ∈ Ioc 0 n | a ∈ A} / n < x + ε := by
  rw [le_iff_forall_pos_lt_add]
  simp only [schnirelmannDensity_lt_iff]

lemma schnirelmannDensity_congr' {B : Set ℕ} [DecidablePred (· ∈ B)]
    (h : ∀ n > 0, n ∈ A ↔ n ∈ B) : schnirelmannDensity A = schnirelmannDensity B := by
  rw [schnirelmannDensity, schnirelmannDensity]; congr; ext ⟨n, hn⟩; congr 3; ext x; simp_all
