/-
Extracted from RingTheory/TwoSidedIdeal/Operations.lean
Genuine: 5 of 5 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Operations on two-sided ideals

This file defines operations on two-sided ideals of a ring `R`.

## Main definitions and results

- `TwoSidedIdeal.span`: the span of `s ⊆ R` is the smallest two-sided ideal containing the set.
- `TwoSidedIdeal.mem_span_iff_mem_addSubgroup_closure_nonunital`: in an associative but non-unital
  ring, an element `x` is in the two-sided ideal spanned by `s` if and only if `x` is in the closure
  of `s ∪ {y * a | y ∈ s, a ∈ R} ∪ {a * y | y ∈ s, a ∈ R} ∪ {a * y * b | y ∈ s, a, b ∈ R}` as an
  additive subgroup.
- `TwoSidedIdeal.mem_span_iff_mem_addSubgroup_closure`: in a unital and associative ring, an
  element  `x` is in the two-sided ideal spanned by `s` if and only if `x` is in the closure of
  `{a*y*b | a, b ∈ R, y ∈ s}` as an additive subgroup.


- `TwoSidedIdeal.comap`: pullback of a two-sided ideal; defined as the preimage of a
  two-sided ideal.
- `TwoSidedIdeal.map`: pushforward of a two-sided ideal; defined as the span of the image of a
  two-sided ideal.
- `TwoSidedIdeal.ker`: the kernel of a ring homomorphism as a two-sided ideal.

- `TwoSidedIdeal.gc`: `fromIdeal` and `asIdeal` form a Galois connection where
  `fromIdeal : Ideal R → TwoSidedIdeal R` is defined as the smallest two-sided ideal containing an
  ideal and `asIdeal : TwoSidedIdeal R → Ideal R` the inclusion map.
-/

namespace TwoSidedIdeal

section NonUnitalNonAssocRing

variable {R S : Type*} [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S]

variable {F : Type*} [FunLike F R S]

variable (f : F)

abbrev span (s : Set R) : TwoSidedIdeal R :=
  { ringCon := ringConGen (fun a b ↦ a - b ∈ s) }

lemma subset_span {s : Set R} : s ⊆ (span s : Set R) := by
  intro x hx
  rw [SetLike.mem_coe, mem_iff]
  exact RingConGen.Rel.of _ _ (by simpa using hx)

lemma mem_span_iff {s : Set R} {x} :
    x ∈ span s ↔ ∀ (I : TwoSidedIdeal R), s ⊆ I → x ∈ I := by
  refine ⟨?_, fun h => h _ subset_span⟩
  delta span
  rw [RingCon.ringConGen_eq]
  intro h I hI
  refine sInf_le (α := RingCon R) ?_ h
  intro x y hxy
  specialize hI hxy
  rwa [SetLike.mem_coe, ← rel_iff] at hI

lemma span_mono {s t : Set R} (h : s ⊆ t) : span s ≤ span t := by
  intro x hx
  rw [mem_span_iff] at hx ⊢
  exact fun I hI => hx I <| h.trans hI

lemma span_le {s : Set R} {I : TwoSidedIdeal R} : span s ≤ I ↔ s ⊆ I := by
  rw [TwoSidedIdeal.ringCon_le_iff, RingCon.gi _ |>.gc]
  exact ⟨fun h x hx ↦ by aesop, fun h x y hxy ↦ (rel_iff I x y).mpr (h hxy)⟩
