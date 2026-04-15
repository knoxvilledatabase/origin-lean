/-
Extracted from Topology/Algebra/InfiniteSum/SummationFilter.lean
Genuine: 7 of 8 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Summation filters

We define a `SummationFilter` on `β` to be a filter on the finite subsets of `β`. These are used
in defining summability: if `L` is a summation filter, we define the `L`-sum of `f` to be the
limit along `L` of the sums over finsets (if this limit exists). This file only develops the basic
machinery of summation filters - the key definitions `HasSum`, `tsum` and `summable` (and their
product variants) are in the file `Mathlib/Topology/Algebra/InfiniteSum/Defs.lean`.
-/

open Set Filter Function

variable {α β γ : Type*}

structure SummationFilter (β) where
  /-- The filter -/
  filter : Filter (Finset β)

namespace SummationFilter

class LeAtTop (L : SummationFilter β) : Prop where
  le_atTop : L.filter ≤ atTop

export LeAtTop (le_atTop)

class NeBot (L : SummationFilter β) : Prop where
  ne_bot : L.filter.NeBot

-- INSTANCE (free from Core): (L

lemma neBot_or_eq_bot (L : SummationFilter β) : L.NeBot ∨ L.filter = ⊥ := by
  by_cases h : L.filter = ⊥
  · exact .inr h
  · exact .inl ⟨⟨h⟩⟩

section support

def support (L : SummationFilter β) : Set β := {b | ∀ᶠ s in L.filter, b ∈ s}

lemma support_eq_limsInf (L : SummationFilter β) :
    support L = limsInf (L.filter.map (↑)) := by
  refine eq_of_forall_ge_iff fun c ↦ ?_
  simpa [support, limsInf, setOf_subset] using
    ⟨fun hL b hb x hx ↦ hL x <| hb.mp <| .of_forall fun c hc ↦ hc hx,
      fun hL x hx ↦ singleton_subset_iff.mp <| hL _ <| by simpa using hx⟩

lemma support_eq_univ_iff {L : SummationFilter β} :
    L.support = univ ↔ L.filter ≤ atTop := by
  simp only [support, Set.eq_univ_iff_forall, Set.mem_setOf]
  refine ⟨fun h s hs ↦ ?_, fun h b ↦ .filter_mono h ?_⟩
  · obtain ⟨t, ht⟩ := mem_atTop_sets.mp hs
    have := (Filter.biInter_finset_mem t).mpr fun b hb ↦ h b
    exact Filter.mem_of_superset this fun r hr ↦ ht r (by simpa using hr)
  · filter_upwards [eventually_ge_atTop {b}] using by simp
