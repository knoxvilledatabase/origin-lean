/-
Extracted from Topology/Semicontinuity/Defs.lean
Genuine: 14 of 15 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Semicontinuous maps

A function `f` from a topological space `α` to an ordered space `β` is *lower semicontinuous* at a
point `x` if, for any `y < f x`, for any `x'` close enough to `x`, one has `f x' > y`. In other
words, `f` can jump up, but it cannot jump down.

*Upper semicontinuous* functions are defined similarly. Upper and lower hemicontinuity (of
functions `f : α → Set β`) are often defined in terms of sequential characterizations, but
here we take an equivalent approach. `f : α → Set β` is *upper hemicontinuous* at `x` if for any
neighborhood of `f x`, `f x'` is included in this neighborhood for all `x'` close enough to `x`.

Of course, one can see a superficial similarity between upper semicontinuity and upper
hemicontinuity. In fact, we can unify all of upper and lower semicontinuity and also upper and
lower hemicontinuity under one umbrella, by considering a general relation `r : α → β → Prop` and
defining semicontinuity of this relation.

This file introduces these notions, and a basic API around them mimicking the API for continuous
functions.

## Main definitions and results

We introduce 4 generic definitions related to semicontinuity:
* `SemicontinuousWithinAt r s x`
* `SemicontinuousAt r x`
* `SemicontinuousOn r s`
* `Semicontinuous r`

We build a basic API using dot notation around these notions, and we prove that
* constant functions are semicontinuous;
* right composition with continuous functions preserves semicontinuity;

We also define lower and upper semicontinuity as abbreviations of these generic definitions
and transfer the generic results to these notions.

## References

* <https://en.wikipedia.org/wiki/Semi-continuity>
* <https://en.wikipedia.org/wiki/Hemicontinuity>

-/

open scoped Topology

open Set Function Filter

variable {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace γ]

/-! ## Main definitions -/

section Semicontinuous

def SemicontinuousWithinAt (r : α → β → Prop) (s : Set α) (x : α) :=
  ∀ y, r x y → ∀ᶠ x' in 𝓝[s] x, r x' y

def SemicontinuousOn (r : α → β → Prop) (s : Set α) :=
  ∀ x ∈ s, SemicontinuousWithinAt r s x

def SemicontinuousAt (r : α → β → Prop) (x : α) : Prop :=
  ∀ y, r x y → ∀ᶠ x' in 𝓝 x, r x' y

def Semicontinuous (r : α → β → Prop) : Prop :=
  ∀ x, SemicontinuousAt r x

variable {r r' : α → β → Prop} {x : α} {s t : Set α}

lemma semicontinuousWithinAt_iff_frequently :
    SemicontinuousWithinAt r s x ↔ ∀ y, (∃ᶠ x' in 𝓝[s] x, ¬ r x' y) → ¬ r x y := by
  simp only [← not_eventually, not_imp_not, SemicontinuousWithinAt]

lemma semicontinuousOn_iff_frequently :
    SemicontinuousOn r s ↔ ∀ x ∈ s, ∀ y, (∃ᶠ x' in 𝓝[s] x, ¬ r x' y) → ¬ r x y := by
  simp only [← not_eventually, not_imp_not, SemicontinuousWithinAt, SemicontinuousOn]

lemma semicontinuousAt_iff_frequently :
    SemicontinuousAt r x ↔ ∀ y, (∃ᶠ x' in 𝓝 x, ¬ r x' y) → ¬ r x y := by
  simp only [← not_eventually, not_imp_not, SemicontinuousAt]

lemma semicontinuous_iff_frequently :
    Semicontinuous r ↔ ∀ x y, (∃ᶠ x' in 𝓝 x, ¬ r x' y) → ¬ r x y := by
  simp only [← not_eventually, not_imp_not, Semicontinuous, SemicontinuousAt]

theorem SemicontinuousWithinAt.mono (h : SemicontinuousWithinAt r s x) (hst : t ⊆ s) :
    SemicontinuousWithinAt r t x := fun y hy =>
  Filter.Eventually.filter_mono (nhdsWithin_mono _ hst) (h y hy)

theorem SemicontinuousWithinAt.congr_of_eventuallyEq {a : α}
    (h : SemicontinuousWithinAt r s a)
    (has : a ∈ s) (hfg : ∀ᶠ x in 𝓝[s] a, ∀ y, r x y ↔ r' x y) :
    SemicontinuousWithinAt r' s a := by
  intro b hb
  simp_rw [← propext_iff, ← funext_iff] at hfg
  rw [← Filter.EventuallyEq.eq_of_nhdsWithin hfg has] at hb
  filter_upwards [hfg, h b hb] with x hx hxb
  exact hx ▸ hxb

theorem semicontinuousWithinAt_univ_iff :
    SemicontinuousWithinAt r univ x ↔ SemicontinuousAt r x := by
  simp [SemicontinuousWithinAt, SemicontinuousAt, nhdsWithin_univ]

theorem SemicontinuousAt.semicontinuousWithinAt (s : Set α)
    (h : SemicontinuousAt r x) : SemicontinuousWithinAt r s x := fun y hy =>
  Filter.Eventually.filter_mono nhdsWithin_le_nhds (h y hy)

theorem SemicontinuousOn.mono (h : SemicontinuousOn r s) (hst : t ⊆ s) :
    SemicontinuousOn r t := fun x hx => (h x (hst hx)).mono hst

theorem semicontinuousOn_univ_iff : SemicontinuousOn r univ ↔ Semicontinuous r := by
  simp [SemicontinuousOn, Semicontinuous, semicontinuousWithinAt_univ_iff]
