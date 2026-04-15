/-
Extracted from Topology/CWComplex/Classical/Subcomplex.lean
Genuine: 6 of 6 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Subcomplexes

In this file we discuss subcomplexes of CW complexes.
The definition of subcomplexes is in the file `Mathlib/Topology/CWComplex/Classical/Basic.lean`.

## Main results
* `RelCWComplex.Subcomplex.instRelCWComplex`: a subcomplex of a (relative) CW complex is again a
  (relative) CW complex.

## References
* [K. Jänich, *Topology*][Janich1984]
-/

noncomputable section

open Metric Set

namespace Topology

variable {X : Type*} [t : TopologicalSpace X] {C D : Set X}

lemma RelCWComplex.Subcomplex.closedCell_subset_of_mem [T2Space X] [RelCWComplex C D]
    (E : Subcomplex C) {n : ℕ} {i : cell C n} (hi : i ∈ E.I n) :
    closedCell n i ⊆ E := by
  rw [← closure_openCell_eq_closedCell, E.closed.closure_subset_iff, ← E.union]
  apply subset_union_of_subset_right
  exact subset_iUnion_of_subset n
    (subset_iUnion (fun (j : ↑(E.I n)) ↦ openCell (C := C) n j) ⟨i, hi⟩)

lemma RelCWComplex.Subcomplex.openCell_subset_of_mem [T2Space X] [RelCWComplex C D]
    (E : Subcomplex C) {n : ℕ} {i : cell C n} (hi : i ∈ E.I n) :
    openCell n i ⊆ E :=
  (openCell_subset_closedCell n i).trans (closedCell_subset_of_mem E hi)

lemma RelCWComplex.Subcomplex.cellFrontier_subset_of_mem [T2Space X] [RelCWComplex C D]
    (E : Subcomplex C) {n : ℕ} {i : cell C n} (hi : i ∈ E.I n) :
    cellFrontier n i ⊆ E :=
  (cellFrontier_subset_closedCell n i).trans (closedCell_subset_of_mem E hi)

lemma RelCWComplex.Subcomplex.union_closedCell [T2Space X] [RelCWComplex C D] (E : Subcomplex C) :
    D ∪ ⋃ (n : ℕ) (j : E.I n), closedCell (C := C) n j = E := by
  apply subset_antisymm
  · apply union_subset E.base_subset
    exact iUnion₂_subset fun n i ↦ closedCell_subset_of_mem E i.2
  · rw [← E.union]
    apply union_subset_union_right
    apply iUnion₂_mono fun n i ↦ ?_
    exact openCell_subset_closedCell (C := C) n i

lemma CWComplex.Subcomplex.union_closedCell [T2Space X] [CWComplex C] (E : Subcomplex C) :
    ⋃ (n : ℕ) (j : E.I n), closedCell (C := C) n j = E :=
  (empty_union _).symm.trans (RelCWComplex.Subcomplex.union_closedCell E)

lemma RelCWComplex.Subcomplex.disjoint_openCell_subcomplex_of_not_mem [RelCWComplex C D]
    (E : Subcomplex C) {n : ℕ} {i : cell C n} (h : i ∉ E.I n) : Disjoint (openCell n i) E := by
  simp_rw [← union, disjoint_union_right, disjoint_iUnion_right]
  exact ⟨disjointBase n i , fun _ _ ↦ disjoint_openCell_of_ne (by lia)⟩

open Classical in
