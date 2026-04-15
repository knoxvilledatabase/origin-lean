/-
Extracted from Combinatorics/SetFamily/Shatter.lean
Genuine: 5 of 8 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Shattering families

This file defines the shattering property and VC-dimension of set families.

## Main declarations

* `Finset.Shatters`: The shattering property.
* `Finset.shatterer`: The set family of sets shattered by a set family.
* `Finset.vcDim`: The Vapnik-Chervonenkis dimension.

## TODO

* Order-shattering
* Strong shattering
-/

open scoped FinsetFamily

namespace Finset

variable {α : Type*} [DecidableEq α] {𝒜 ℬ : Finset (Finset α)} {s t : Finset α} {a : α}

def Shatters (𝒜 : Finset (Finset α)) (s : Finset α) : Prop := ∀ ⦃t⦄, t ⊆ s → ∃ u ∈ 𝒜, s ∩ u = t

-- INSTANCE (free from Core): :

lemma Shatters.exists_inter_eq_singleton (hs : Shatters 𝒜 s) (ha : a ∈ s) : ∃ t ∈ 𝒜, s ∩ t = {a} :=
  hs <| singleton_subset_iff.2 ha

lemma Shatters.mono_left (h : 𝒜 ⊆ ℬ) (h𝒜 : 𝒜.Shatters s) : ℬ.Shatters s :=
  fun _t ht ↦ let ⟨u, hu, hut⟩ := h𝒜 ht; ⟨u, h hu, hut⟩

lemma Shatters.mono_right (h : t ⊆ s) (hs : 𝒜.Shatters s) : 𝒜.Shatters t := fun u hu ↦ by
  obtain ⟨v, hv, rfl⟩ := hs (hu.trans h); exact ⟨v, hv, inf_congr_right hu <| inf_le_of_left_le h⟩

lemma shatters_of_forall_subset (h : ∀ t, t ⊆ s → t ∈ 𝒜) : 𝒜.Shatters s :=
  fun t ht ↦ ⟨t, h _ ht, inter_eq_right.2 ht⟩
