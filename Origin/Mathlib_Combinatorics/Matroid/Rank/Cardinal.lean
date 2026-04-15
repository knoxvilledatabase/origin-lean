/-
Extracted from Combinatorics/Matroid/Rank/Cardinal.lean
Genuine: 11 of 11 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Cardinal-valued rank

In a finitary matroid, all bases have the same cardinality.
In fact, something stronger holds: if each of `I` and `J` is a basis for a set `X`,
then `#(I \ J) = #(J \ I)` and (consequently) `#I = #J`.
This file introduces a typeclass `InvariantCardinalRank` that applies to any matroid
such that this property holds for all `I`, `J` and `X`.

A matroid satisfying this condition has a well-defined cardinality-valued rank function,
both for itself and all its minors.

## Main Declarations

* `Matroid.InvariantCardinalRank` : a typeclass capturing the idea that a matroid and all its minors
  have a well-behaved cardinal-valued rank function.
* `Matroid.cRank M` is the supremum of the cardinalities of the bases of matroid `M`.
* `Matroid.cRk M X` is the supremum of the cardinalities of the bases of a set `X` in a matroid `M`.
* `invariantCardinalRank_of_finitary` is the instance
  showing that `Finitary` matroids are `InvariantCardinalRank`.
* `cRk_inter_add_cRk_union_le` states that cardinal rank is submodular.

## Notes

It is not (provably) the case that all matroids are `InvariantCardinalRank`,
since the equicardinality of bases in general matroids is independent of ZFC
(see the module docstring of `Mathlib/Combinatorics/Matroid/Basic.lean`).
Lemmas like `Matroid.Base.cardinalMk_diff_comm` become true for all matroids
only if they are weakened by replacing `Cardinal.mk` with the cruder `ℕ∞`-valued `Set.encard`.
The `ℕ∞`-valued rank and rank functions `Matroid.eRank` and `Matroid.eRk`,
which have a more unconditionally strong API,
are developed in `Mathlib/Combinatorics/Matroid/Rank/ENat.lean`.

## Implementation Details

Since the functions `cRank` and `cRk` are defined as suprema,
independently of the `Matroid.InvariantCardinalRank` typeclass,
they are well-defined for all matroids.
However, for matroids that do not satisfy `InvariantCardinalRank`, they are badly behaved.
For instance, in general `cRk` is not submodular,
and its value may differ on a set `X` and the closure of `X`.
We state and prove theorems without `InvariantCardinalRank` whenever possible,
which sometime makes their proofs longer than they would be with the instance.

## TODO

* Higgs' theorem : if the generalized continuum hypothesis holds,
  then every matroid is `InvariantCardinalRank`.

-/

universe u v

variable {α : Type u} {β : Type v} {f : α → β} {M : Matroid α} {I J B B' X Y : Set α}

open Cardinal Set

namespace Matroid

section Rank

variable {κ : Cardinal}

noncomputable def cRank (M : Matroid α) := ⨆ B : {B // M.IsBase B}, #B

noncomputable def cRk (M : Matroid α) (X : Set α) := (M ↾ X).cRank

theorem IsBase.cardinalMk_le_cRank (hB : M.IsBase B) : #B ≤ M.cRank :=
  le_ciSup (f := fun B : {B // M.IsBase B} ↦ #B.1) (bddAbove_range _) ⟨B, hB⟩

theorem Indep.cardinalMk_le_cRank (ind : M.Indep I) : #I ≤ M.cRank :=
  have ⟨B, isBase, hIB⟩ := ind.exists_isBase_superset
  le_ciSup_of_le (bddAbove_range _) ⟨B, isBase⟩ (mk_le_mk_of_subset hIB)

theorem cRank_eq_iSup_cardinalMk_indep : M.cRank = ⨆ I : {I // M.Indep I}, #I :=
  (ciSup_le' fun B ↦ le_ciSup_of_le (bddAbove_range _) ⟨B, B.2.indep⟩ <| by rfl).antisymm <|
    ciSup_le' fun I ↦
      have ⟨B, isBase, hIB⟩ := I.2.exists_isBase_superset
      le_ciSup_of_le (bddAbove_range _) ⟨B, isBase⟩ (mk_le_mk_of_subset hIB)

theorem IsBasis'.cardinalMk_le_cRk (hIX : M.IsBasis' I X) : #I ≤ M.cRk X :=
  (isBase_restrict_iff'.2 hIX).cardinalMk_le_cRank

theorem IsBasis.cardinalMk_le_cRk (hIX : M.IsBasis I X) : #I ≤ M.cRk X :=
  hIX.isBasis'.cardinalMk_le_cRk

theorem cRank_le_iff : M.cRank ≤ κ ↔ ∀ ⦃B⦄, M.IsBase B → #B ≤ κ :=
  ⟨fun h _ hB ↦ (hB.cardinalMk_le_cRank.trans h), fun h ↦ ciSup_le fun ⟨_, hB⟩ ↦ h hB⟩

theorem cRk_le_iff : M.cRk X ≤ κ ↔ ∀ ⦃I⦄, M.IsBasis' I X → #I ≤ κ := by
  simp_rw [cRk, cRank_le_iff, isBase_restrict_iff']

theorem Indep.cardinalMk_le_cRk_of_subset (hI : M.Indep I) (hIX : I ⊆ X) : #I ≤ M.cRk X :=
  let ⟨_, hJ, hIJ⟩ := hI.subset_isBasis'_of_subset hIX
  (mk_le_mk_of_subset hIJ).trans hJ.cardinalMk_le_cRk

theorem cRk_le_cardinalMk (M : Matroid α) (X : Set α) : M.cRk X ≤ #X :=
  ciSup_le fun ⟨_, hI⟩ ↦ mk_le_mk_of_subset hI.subset_ground
