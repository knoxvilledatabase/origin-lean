/-
Extracted from MeasureTheory/OuterMeasure/AE.lean
Genuine: 12 of 19 | Dissolved: 3 | Infrastructure: 4
-/
import Origin.Core

/-!
# The “almost everywhere” filter of co-null sets.

If `μ` is an outer measure or a measure on `α`,
then `MeasureTheory.ae μ` is the filter of co-null sets: `s ∈ ae μ ↔ μ sᶜ = 0`.

In this file we define the filter and prove some basic theorems about it.

## Notation

- `∀ᵐ x ∂μ, p x`: the predicate `p` holds for `μ`-a.e. all `x`;
- `∃ᶠ x ∂μ, p x`: the predicate `p` holds on a set of nonzero measure;
- `f =ᵐ[μ] g`: `f x = g x` for `μ`-a.e. all `x`;
- `f ≤ᵐ[μ] g`: `f x ≤ g x` for `μ`-a.e. all `x`.

## Implementation details

All notation introduced in this file
reducibly unfolds to the corresponding definitions about filters,
so generic lemmas about `Filter.Eventually`, `Filter.EventuallyEq` etc. apply.
However, we restate some lemmas specifically for `ae`.

## Tags

outer measure, measure, almost everywhere
-/

open Filter Set

open scoped ENNReal

namespace MeasureTheory

variable {α β F : Type*} [FunLike F (Set α) ℝ≥0∞] [OuterMeasureClass F α] {μ : F} {s t : Set α}

def ae (μ : F) : Filter α :=
  .ofCountableUnion (μ · = 0) (fun _S hSc ↦ (measure_sUnion_null_iff hSc).2) fun _t ht _s hs ↦
    measure_mono_null hs ht

deriving CountableInterFilter

notation3 "∀ᵐ "(...)" ∂"μ", "r:(scoped p => Filter.Eventually p <| MeasureTheory.ae μ) => r

notation3 "∃ᵐ "(...)" ∂"μ", "r:(scoped P => Filter.Frequently P <| MeasureTheory.ae μ) => r

notation:50 f " =ᵐ[" μ:50 "] " g:50 => Filter.EventuallyEq (MeasureTheory.ae μ) f g

notation:50 f " ≤ᵐ[" μ:50 "] " g:50 => Filter.EventuallyLE (MeasureTheory.ae μ) f g

theorem compl_mem_ae_iff {s : Set α} : sᶜ ∈ ae μ ↔ μ s = 0 := by simp only [mem_ae_iff, compl_compl]

-- DISSOLVED: frequently_ae_iff

-- DISSOLVED: frequently_ae_mem_iff

theorem measure_eq_zero_iff_ae_notMem {s : Set α} : μ s = 0 ↔ ∀ᵐ a ∂μ, a ∉ s :=
  compl_mem_ae_iff.symm

theorem ae_of_all {p : α → Prop} (μ : F) : (∀ a, p a) → ∀ᵐ a ∂μ, p a :=
  Eventually.of_forall

theorem ae_all_iff {ι : Sort*} [Countable ι] {p : α → ι → Prop} :
    (∀ᵐ a ∂μ, ∀ i, p a i) ↔ ∀ i, ∀ᵐ a ∂μ, p a i :=
  eventually_countable_forall

theorem all_ae_of {ι : Sort*} {p : α → ι → Prop} (hp : ∀ᵐ a ∂μ, ∀ i, p a i) (i : ι) :
    ∀ᵐ a ∂μ, p a i := by
  filter_upwards [hp] with a ha using ha i

-- DISSOLVED: ae_iff_of_countable

theorem ae_ball_iff {ι : Type*} {S : Set ι} (hS : S.Countable) {p : α → ∀ i ∈ S, Prop} :
    (∀ᵐ x ∂μ, ∀ i (hi : i ∈ S), p x i hi) ↔ ∀ i (hi : i ∈ S), ∀ᵐ x ∂μ, p x i hi :=
  eventually_countable_ball hS

lemma ae_eq_refl (f : α → β) : f =ᵐ[μ] f := EventuallyEq.rfl

lemma ae_eq_rfl {f : α → β} : f =ᵐ[μ] f := EventuallyEq.rfl

lemma ae_eq_comm {f g : α → β} : f =ᵐ[μ] g ↔ g =ᵐ[μ] f := eventuallyEq_comm

theorem ae_eq_trans {f g h : α → β} (h₁ : f =ᵐ[μ] g) (h₂ : g =ᵐ[μ] h) : f =ᵐ[μ] h :=
  h₁.trans h₂

lemma _root_.Set.EqOn.aeEq {f g : α → β} (h : s.EqOn f g) (h2 : μ sᶜ = 0) : f =ᵐ[μ] g :=
  eventuallyEq_of_mem h2 h
