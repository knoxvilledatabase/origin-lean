/-
Extracted from Analysis/Normed/Lp/lpSpace.lean
Genuine: 17 of 20 | Dissolved: 3 | Infrastructure: 0
-/
import Origin.Core

/-!
# ℓp space

This file describes properties of elements `f` of a pi-type `∀ i, E i` with finite "norm",
defined for `p : ℝ≥0∞` as the size of the support of `f` if `p=0`, `(∑' a, ‖f a‖^p) ^ (1/p)` for
`0 < p < ∞` and `⨆ a, ‖f a‖` for `p=∞`.

The Prop-valued `Memℓp f p` states that a function `f : ∀ i, E i` has finite norm according
to the above definition; that is, `f` has finite support if `p = 0`, `Summable (fun a ↦ ‖f a‖^p)` if
`0 < p < ∞`, and `BddAbove (norm '' (Set.range f))` if `p = ∞`.

The space `lp E p` is the subtype of elements of `∀ i : α, E i` which satisfy `Memℓp f p`. For
`1 ≤ p`, the "norm" is genuinely a norm and `lp` is a complete metric space.

## Main definitions

* `Memℓp f p` : property that the function `f` satisfies, as appropriate, `f` finitely supported
  if `p = 0`, `Summable (fun a ↦ ‖f a‖^p)` if `0 < p < ∞`, and `BddAbove (norm '' (Set.range f))` if
  `p = ∞`.
* `lp E p` : elements of `∀ i : α, E i` such that `Memℓp f p`. Defined as an `AddSubgroup` of
  a type synonym `PreLp` for `∀ i : α, E i`, and equipped with a `NormedAddCommGroup` structure.
  Under appropriate conditions, this is also equipped with the instances `lp.normedSpace`,
  `lp.completeSpace`. For `p=∞`, there is also `lp.inftyNormedRing`,
  `lp.inftyNormedAlgebra`, `lp.inftyStarRing` and `lp.inftyCStarRing`.

## Main results

* `Memℓp.of_exponent_ge`: For `q ≤ p`, a function which is `Memℓp` for `q` is also `Memℓp` for `p`.
* `lp.memℓp_of_tendsto`, `lp.norm_le_of_tendsto`: A pointwise limit of functions in `lp`, all with
  `lp` norm `≤ C`, is itself in `lp` and has `lp` norm `≤ C`.
* `lp.tsum_mul_le_mul_norm`: basic form of Hölder's inequality

## Implementation

Since `lp` is defined as an `AddSubgroup`, dot notation does not work. Use `lp.norm_neg f` to
say that `‖-f‖ = ‖f‖`, instead of the non-working `f.norm_neg`.

## TODO

* More versions of Hölder's inequality (for example: the case `p = 1`, `q = ∞`; a version for normed
  rings which has `‖∑' i, f i * g i‖` rather than `∑' i, ‖f i‖ * g i‖` on the RHS; a version for
  three exponents satisfying `1 / r = 1 / p + 1 / q`)

-/

noncomputable section

open scoped NNReal ENNReal Function

variable {𝕜 𝕜' : Type*} {α : Type*} {E : α → Type*} {p q : ℝ≥0∞} [∀ i, NormedAddCommGroup (E i)]

/-!
### `Memℓp` predicate

-/

def Memℓp (f : ∀ i, E i) (p : ℝ≥0∞) : Prop :=
  if p = 0 then Set.Finite { i | f i ≠ 0 }
  else if p = ∞ then BddAbove (Set.range fun i => ‖f i‖)
  else Summable fun i => ‖f i‖ ^ p.toReal

-- DISSOLVED: memℓp_zero_iff

-- DISSOLVED: memℓp_zero

theorem memℓp_infty_iff {f : ∀ i, E i} : Memℓp f ∞ ↔ BddAbove (Set.range fun i => ‖f i‖) := by
  simp [Memℓp]

theorem memℓp_infty {f : ∀ i, E i} (hf : BddAbove (Set.range fun i => ‖f i‖)) : Memℓp f ∞ :=
  memℓp_infty_iff.2 hf

theorem memℓp_gen_iff (hp : 0 < p.toReal) {f : ∀ i, E i} :
    Memℓp f p ↔ Summable fun i => ‖f i‖ ^ p.toReal := by
  rw [ENNReal.toReal_pos_iff] at hp
  dsimp [Memℓp]
  rw [if_neg hp.1.ne', if_neg hp.2.ne]

theorem memℓp_gen {f : ∀ i, E i} (hf : Summable fun i => ‖f i‖ ^ p.toReal) : Memℓp f p := by
  rcases p.trichotomy with (rfl | rfl | hp)
  · apply memℓp_zero
    have H : Summable fun _ : α => (1 : ℝ) := by simpa using hf
    exact (Set.Finite.of_summable_const (by simp) H).subset (Set.subset_univ _)
  · apply memℓp_infty
    have H : Summable fun _ : α => (1 : ℝ) := by simpa using hf
    simpa using ((Set.Finite.of_summable_const (by simp) H).image fun i => ‖f i‖).bddAbove
  exact (memℓp_gen_iff hp).2 hf

theorem memℓp_gen' {C : ℝ} {f : ∀ i, E i} (hf : ∀ s : Finset α, ∑ i ∈ s, ‖f i‖ ^ p.toReal ≤ C) :
    Memℓp f p := by
  apply memℓp_gen
  use ⨆ s : Finset α, ∑ i ∈ s, ‖f i‖ ^ p.toReal
  apply hasSum_of_isLUB_of_nonneg
  · intro b
    positivity
  apply isLUB_ciSup
  use C
  rintro - ⟨s, rfl⟩
  exact hf s

theorem memℓp_gen_iff' {f : (i : α) → E i} (hp : 0 < p.toReal) :
    Memℓp f p ↔ ∀ (s : Finset α), ∑ i ∈ s, ‖f i‖ ^ p.toReal ≤ ∑' i, ‖f i‖ ^ p.toReal := by
  refine ⟨fun hf ↦ ?_, memℓp_gen'⟩
  obtain ⟨hp₁, hp₂⟩ := ENNReal.toReal_pos_iff.mp hp
  simp only [Memℓp, hp₁.ne', ↓reduceIte, hp₂.ne] at hf
  simpa [upperBounds] using isLUB_hasSum (by intro; positivity) hf.hasSum |>.1

theorem memℓp_gen_iff'' {f : (i : α) → E i} (hp : 0 < p.toReal) :
    Memℓp f p ↔ ∃ C, 0 ≤ C ∧ ∀ (s : Finset α), ∑ i ∈ s, ‖f i‖ ^ p.toReal ≤ C := by
  refine ⟨fun hf ↦ ?_, fun ⟨C, _, hC⟩ ↦ memℓp_gen' hC⟩
  exact ⟨_, tsum_nonneg fun i ↦ (by positivity), memℓp_gen_iff' hp |>.mp hf⟩

theorem zero_memℓp : Memℓp (0 : ∀ i, E i) p := by
  rcases p.trichotomy with (rfl | rfl | hp)
  · apply memℓp_zero
    simp
  · apply memℓp_infty
    simp only [norm_zero, Pi.zero_apply]
    exact bddAbove_singleton.mono Set.range_const_subset
  · apply memℓp_gen
    simp [Real.zero_rpow hp.ne', summable_zero]

theorem zero_mem_ℓp' : Memℓp (fun i : α => (0 : E i)) p :=
  zero_memℓp

theorem memℓp_norm_iff {f : (i : α) → E i} :
    Memℓp (‖f ·‖) p ↔ Memℓp f p := by
  obtain (rfl | rfl | hp) := p.trichotomy
  · simp [memℓp_zero_iff]
  · simp [memℓp_infty_iff]
  · simp [memℓp_gen_iff hp]

alias ⟨Memℓp.of_norm, Memℓp.norm⟩ := memℓp_norm_iff

namespace Memℓp

theorem mono {f : (i : α) → E i} {g : α → ℝ}
    (hg : Memℓp g p) (hfg : ∀ i, ‖f i‖ ≤ g i) :
    Memℓp f p := by
  replace hfg (i) : ‖f i‖ ≤ ‖g i‖ := (hfg i).trans (Real.le_norm_self _)
  obtain (rfl | rfl | hp) := p.trichotomy
  · simp_rw [memℓp_zero_iff, ← norm_pos_iff] at hg ⊢
    refine hg.subset fun i hi ↦ hi.trans_le <| hfg i
  · rw [memℓp_infty_iff] at hg ⊢
    exact hg.range_mono _ hfg
  · rw [memℓp_gen_iff hp] at hg ⊢
    apply hg.of_norm_bounded fun i ↦ ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    gcongr
    exact hfg i

theorem mono' {F : α → Type*} [∀ i, NormedAddCommGroup (F i)] {f : (i : α) → E i}
    {g : (i : α) → F i} (hg : Memℓp g p) (hfg : ∀ i, ‖f i‖ ≤ ‖g i‖) :
    Memℓp f p :=
  hg.norm.mono hfg

-- DISSOLVED: finite_dsupport

theorem bddAbove {f : ∀ i, E i} (hf : Memℓp f ∞) : BddAbove (Set.range fun i => ‖f i‖) :=
  memℓp_infty_iff.1 hf

theorem summable (hp : 0 < p.toReal) {f : ∀ i, E i} (hf : Memℓp f p) :
    Summable fun i => ‖f i‖ ^ p.toReal :=
  (memℓp_gen_iff hp).1 hf

lemma summable_of_one {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {x : α → E} (hx : Memℓp x 1) : Summable x :=
  .of_norm <| by simpa using hx.summable

theorem neg {f : ∀ i, E i} (hf : Memℓp f p) : Memℓp (-f) p := by
  rcases p.trichotomy with (rfl | rfl | hp)
  · apply memℓp_zero
    simp [hf.finite_dsupport]
  · apply memℓp_infty
    simpa using hf.bddAbove
  · apply memℓp_gen
    simpa using hf.summable hp
