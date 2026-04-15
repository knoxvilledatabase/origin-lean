/-
Extracted from MeasureTheory/Constructions/EventuallyMeasurable.lean
Genuine: 11 | Conflates: 0 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Order.Filter.CountableInter

/-!
# Measurability modulo a filter

In this file we consider the general notion of measurability modulo a σ-filter.
Two important instances of this construction are null-measurability with respect to a measure,
where the filter is the collection of co-null sets, and
Baire-measurability with respect to a topology,
where the filter is the collection of comeager (residual) sets.
(not to be confused with measurability with respect to the sigma algebra
of Baire sets, which is sometimes also called this.)
TODO: Implement the latter.

## Main definitions

* `EventuallyMeasurableSpace`: A `MeasurableSpace` on a type `α` consisting of sets which are
  `Filter.EventuallyEq` to a measurable set with respect to a given `CountableInterFilter` on `α`
  and `MeasurableSpace` on `α`.
* `EventuallyMeasurableSet`: A `Prop` for sets which are measurable with respect to some
  `EventuallyMeasurableSpace`.
* `EventuallyMeasurable`: A `Prop` for functions which are measurable with respect to some
  `EventuallyMeasurableSpace` on the domain.

-/

open Filter Set MeasurableSpace

variable {α : Type*} (m : MeasurableSpace α) {s t : Set α}

def EventuallyMeasurableSpace (l : Filter α) [CountableInterFilter l] : MeasurableSpace α where
  MeasurableSet' s := ∃ t, MeasurableSet t ∧ s =ᶠ[l] t
  measurableSet_empty := ⟨∅, MeasurableSet.empty, EventuallyEq.refl _ _ ⟩
  measurableSet_compl := fun _ ⟨t, ht, hts⟩ => ⟨tᶜ, ht.compl, hts.compl⟩
  measurableSet_iUnion s hs := by
    choose t ht hts using hs
    exact ⟨⋃ i, t i, MeasurableSet.iUnion ht, EventuallyEq.countable_iUnion hts⟩

def EventuallyMeasurableSet (l : Filter α) [CountableInterFilter l]  (s : Set α) : Prop :=
  @MeasurableSet _ (EventuallyMeasurableSpace m l) s

variable {l : Filter α} [CountableInterFilter l]

variable {m}

theorem MeasurableSet.eventuallyMeasurableSet (hs : MeasurableSet s) :
    EventuallyMeasurableSet m l s :=
  ⟨s, hs, EventuallyEq.refl _ _⟩

theorem EventuallyMeasurableSpace.measurable_le : m ≤ EventuallyMeasurableSpace m l :=
  fun _ hs => hs.eventuallyMeasurableSet

theorem eventuallyMeasurableSet_of_mem_filter (hs : s ∈ l) : EventuallyMeasurableSet m l s :=
  ⟨univ, MeasurableSet.univ, eventuallyEq_univ.mpr hs⟩

theorem EventuallyMeasurableSet.congr
    (ht : EventuallyMeasurableSet m l t) (hst : s =ᶠ[l] t) : EventuallyMeasurableSet m l s := by
  rcases ht with ⟨t', ht', htt'⟩
  exact ⟨t', ht', hst.trans htt'⟩

section instances

namespace EventuallyMeasurableSpace

instance measurableSingleton [MeasurableSingletonClass α] :
    @MeasurableSingletonClass α (EventuallyMeasurableSpace m l) :=
  @MeasurableSingletonClass.mk _ (_) <| fun x => (MeasurableSet.singleton x).eventuallyMeasurableSet

end EventuallyMeasurableSpace

end instances

section EventuallyMeasurable

open Function

variable (m l) {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]

def EventuallyMeasurable (f : α → β) : Prop := @Measurable _ _ (EventuallyMeasurableSpace m l) _ f

variable {m l} {f g : α → β} {h : β → γ}

theorem Measurable.eventuallyMeasurable (hf : Measurable f) : EventuallyMeasurable m l f :=
  hf.le EventuallyMeasurableSpace.measurable_le

theorem Measurable.comp_eventuallyMeasurable (hh : Measurable h) (hf : EventuallyMeasurable m l f) :
    EventuallyMeasurable m l (h ∘ f) :=
  hh.comp hf

theorem EventuallyMeasurable.congr
    (hf : EventuallyMeasurable m l f) (hgf : g =ᶠ[l] f) : EventuallyMeasurable m l g :=
  fun _ hs => EventuallyMeasurableSet.congr (hf hs)
    (hgf.preimage _)

theorem Measurable.eventuallyMeasurable_of_eventuallyEq
    (hf : Measurable f) (hgf : g =ᶠ[l] f) : EventuallyMeasurable m l g :=
  hf.eventuallyMeasurable.congr hgf

end EventuallyMeasurable
