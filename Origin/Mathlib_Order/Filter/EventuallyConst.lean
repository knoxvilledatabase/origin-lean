/-
Extracted from Order/Filter/EventuallyConst.lean
Genuine: 11 of 12 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Functions that are eventually constant along a filter

In this file we define a predicate `Filter.EventuallyConst f l` saying that a function `f : α → β`
is eventually equal to a constant along a filter `l`. We also prove some basic properties of these
functions.

## Implementation notes

A naive definition of `Filter.EventuallyConst f l` is `∃ y, ∀ᶠ x in l, f x = y`.
However, this proposition is false for empty `α`, `β`.
Instead, we say that `Filter.map f l` is supported on a subsingleton.
This allows us to drop `[Nonempty _]` assumptions here and there.
-/

open Set

variable {α β γ δ : Type*} {l : Filter α} {f : α → β}

namespace Filter

def EventuallyConst (f : α → β) (l : Filter α) : Prop := (map f l).Subsingleton

theorem HasBasis.eventuallyConst_iff {ι : Sort*} {p : ι → Prop} {s : ι → Set α}
    (h : l.HasBasis p s) : EventuallyConst f l ↔ ∃ i, p i ∧ ∀ x ∈ s i, ∀ y ∈ s i, f x = f y :=
  (h.map f).subsingleton_iff.trans <| by simp only [Set.Subsingleton, forall_mem_image]

lemma eventuallyConst_iff_tendsto [Nonempty β] :
    EventuallyConst f l ↔ ∃ x, Tendsto f l (pure x) :=
  subsingleton_iff_exists_le_pure

alias ⟨EventuallyConst.exists_tendsto, _⟩ := eventuallyConst_iff_tendsto

theorem EventuallyConst.of_tendsto {x : β} (h : Tendsto f l (pure x)) : EventuallyConst f l :=
  have : Nonempty β := ⟨x⟩; eventuallyConst_iff_tendsto.2 ⟨x, h⟩

theorem eventuallyConst_iff_exists_eventuallyEq [Nonempty β] :
    EventuallyConst f l ↔ ∃ c, f =ᶠ[l] fun _ ↦ c :=
  subsingleton_iff_exists_singleton_mem

alias ⟨EventuallyConst.eventuallyEq_const, _⟩ := eventuallyConst_iff_exists_eventuallyEq

theorem eventuallyConst_pred' {p : α → Prop} :
    EventuallyConst p l ↔ (p =ᶠ[l] fun _ ↦ False) ∨ (p =ᶠ[l] fun _ ↦ True) := by
  simp only [eventuallyConst_iff_exists_eventuallyEq, Prop.exists_iff]

theorem eventuallyConst_pred {p : α → Prop} :
    EventuallyConst p l ↔ (∀ᶠ x in l, p x) ∨ (∀ᶠ x in l, ¬p x) := by
  simp [eventuallyConst_pred', or_comm, EventuallyEq]

theorem eventuallyConst_set' {s : Set α} :
    EventuallyConst s l ↔ (s =ᶠ[l] (∅ : Set α)) ∨ s =ᶠ[l] univ :=
  eventuallyConst_pred'

theorem eventuallyConst_set {s : Set α} :
    EventuallyConst s l ↔ (∀ᶠ x in l, x ∈ s) ∨ (∀ᶠ x in l, x ∉ s) :=
  eventuallyConst_pred

theorem eventuallyConst_preimage {s : Set β} {f : α → β} :
    EventuallyConst (f ⁻¹' s) l ↔ EventuallyConst s (map f l) :=
  .rfl

theorem EventuallyEq.eventuallyConst_iff {g : α → β} (h : f =ᶠ[l] g) :
    EventuallyConst f l ↔ EventuallyConst g l := by
  simp only [EventuallyConst, map_congr h]
