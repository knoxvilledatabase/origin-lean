/-
Extracted from Algebra/Polynomial/Lifts.lean
Genuine: 15 of 16 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Polynomials that lift

Given semirings `R` and `S` with a morphism `f : R →+* S`, we define a subsemiring `lifts` of
`S[X]` by the image of `RingHom.of (map f)`.
Then, we prove that a polynomial that lifts can always be lifted to a polynomial of the same degree
and that a monic polynomial that lifts can be lifted to a monic polynomial (of the same degree).

## Main definition

* `lifts (f : R →+* S)` : the subsemiring of polynomials that lift.

## Main results

* `lifts_and_degree_eq` : A polynomial lifts if and only if it can be lifted to a polynomial
  of the same degree.
* `lifts_and_degree_eq_and_monic` : A monic polynomial lifts if and only if it can be lifted to a
  monic polynomial of the same degree.
* `lifts_iff_alg` : if `R` is commutative, a polynomial lifts if and only if it is in the image of
  `mapAlg`, where `mapAlg : R[X] →ₐ[R] S[X]` is the only `R`-algebra map
  that sends `X` to `X`.

## Implementation details

In general `R` and `S` are semirings, so `lifts` is a semiring. In the case of rings, see
`lifts_iff_liftsRing`.

Since we do not assume `R` to be commutative, we cannot say in general that the set of polynomials
that lift is a subalgebra. (By `lift_iff` this is true if `R` is commutative.)

-/

open Polynomial

noncomputable section

namespace Polynomial

universe u v w

section Semiring

variable {R : Type u} [Semiring R] {S : Type v} [Semiring S] {f : R →+* S}

def lifts (f : R →+* S) : Subsemiring S[X] :=
  RingHom.rangeS (mapRingHom f)

theorem mem_lifts (p : S[X]) : p ∈ lifts f ↔ ∃ q : R[X], map f q = p := by
  simp only [coe_mapRingHom, lifts, RingHom.mem_rangeS]

theorem lifts_iff_set_range (p : S[X]) : p ∈ lifts f ↔ p ∈ Set.range (map f) := by
  simp only [coe_mapRingHom, lifts, Set.mem_range, RingHom.mem_rangeS]

theorem lifts_iff_ringHom_rangeS (p : S[X]) : p ∈ lifts f ↔ p ∈ (mapRingHom f).rangeS := by
  simp only [coe_mapRingHom, lifts, RingHom.mem_rangeS]

theorem lifts_iff_coeff_lifts (p : S[X]) : p ∈ lifts f ↔ ∀ n : ℕ, p.coeff n ∈ Set.range f := by
  rw [lifts_iff_ringHom_rangeS, mem_map_rangeS f]
  rfl

theorem lifts_iff_coeffs_subset_range (p : S[X]) :
    p ∈ lifts f ↔ (p.coeffs : Set S) ⊆ Set.range f := by
  rw [lifts_iff_coeff_lifts]
  constructor
  · intro h _ hc
    obtain ⟨n, ⟨-, hn⟩⟩ := mem_coeffs_iff.mp hc
    exact hn ▸ h n
  · intro h n
    by_cases hn : p.coeff n = 0
    · exact ⟨0, by simp [hn]⟩
    · exact h <| coeff_mem_coeffs hn

theorem C_mem_lifts (f : R →+* S) (r : R) : C (f r) ∈ lifts f :=
  ⟨C r, by
    simp only [coe_mapRingHom, map_C]⟩

theorem C'_mem_lifts {f : R →+* S} {s : S} (h : s ∈ Set.range f) : C s ∈ lifts f := by
  obtain ⟨r, rfl⟩ := Set.mem_range.1 h
  use C r
  simp only [coe_mapRingHom, map_C]

theorem X_mem_lifts (f : R →+* S) : (X : S[X]) ∈ lifts f :=
  ⟨X, by
    simp only [coe_mapRingHom, map_X]⟩

theorem X_pow_mem_lifts (f : R →+* S) (n : ℕ) : (X ^ n : S[X]) ∈ lifts f :=
  ⟨X ^ n, by
    simp only [coe_mapRingHom, map_pow, map_X]⟩

theorem base_mul_mem_lifts {p : S[X]} (r : R) (hp : p ∈ lifts f) : C (f r) * p ∈ lifts f := by
  simp only [lifts, RingHom.mem_rangeS] at hp ⊢
  obtain ⟨p₁, rfl⟩ := hp
  use C r * p₁
  simp only [coe_mapRingHom, map_C, map_mul]

theorem monomial_mem_lifts {s : S} (n : ℕ) (h : s ∈ Set.range f) : monomial n s ∈ lifts f := by
  obtain ⟨r, rfl⟩ := Set.mem_range.1 h
  use monomial n r
  simp only [coe_mapRingHom, map_monomial]

section LiftDeg

theorem monomial_mem_lifts_and_degree_eq {s : S} {n : ℕ} (hl : monomial n s ∈ lifts f) :
    ∃ q : R[X], map f q = monomial n s ∧ q.degree = (monomial n s).degree := by
  rcases eq_or_ne s 0 with rfl | h
  · exact ⟨0, by simp⟩
  obtain ⟨a, rfl⟩ := coeff_monomial_same n s ▸ (monomial n s).lifts_iff_coeff_lifts.mp hl n
  refine ⟨monomial n a, map_monomial f, ?_⟩
  rw [degree_monomial, degree_monomial n h]
  exact mt (fun ha ↦ ha ▸ map_zero f) h

theorem exists_support_eq_of_mem_lifts {p : S[X]} (hlifts : p ∈ lifts f) :
    ∃ q : R[X], map f q = p ∧ q.support = p.support := by
  rw [lifts_iff_coeff_lifts] at hlifts
  let g : ℕ → R := fun k ↦ (hlifts k).choose
  have hg : ∀ k, f (g k) = p.coeff k := fun k ↦ (hlifts k).choose_spec
  let q : R[X] := ∑ k ∈ p.support, monomial k (g k)
  have hq : map f q = p := by simp_rw [q, Polynomial.map_sum, map_monomial, hg, ← as_sum_support]
  have hq' : q.support = p.support := by
    simp_rw [Finset.ext_iff, mem_support_iff, q, finset_sum_coeff, coeff_monomial,
      Finset.sum_ite_eq', ite_ne_right_iff, mem_support_iff, and_iff_left_iff_imp, not_imp_not]
    exact fun k h ↦ by rw [← hg, h, map_zero]
  exact ⟨q, hq, hq'⟩

theorem exists_degree_eq_of_mem_lifts {p : S[X]} (hlifts : p ∈ lifts f) :
    ∃ q : R[X], map f q = p ∧ q.degree = p.degree := by
  obtain ⟨q, hq, hq'⟩ := exists_support_eq_of_mem_lifts hlifts
  exact ⟨q, hq, congrArg Finset.max hq'⟩
