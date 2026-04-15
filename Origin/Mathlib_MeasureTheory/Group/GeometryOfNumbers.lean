/-
Extracted from MeasureTheory/Group/GeometryOfNumbers.lean
Genuine: 1 | Conflates: 0 | Dissolved: 2 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Analysis.Convex.Body
import Mathlib.Analysis.Convex.Measure
import Mathlib.MeasureTheory.Group.FundamentalDomain

/-!
# Geometry of numbers

In this file we prove some of the fundamental theorems in the geometry of numbers, as studied by
Hermann Minkowski.

## Main results

* `exists_pair_mem_lattice_not_disjoint_vadd`: Blichfeldt's principle, existence of two distinct
  points in a subgroup such that the translates of a set by these two points are not disjoint when
  the covolume of the subgroup is larger than the volume of the set.
* `exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure`: Minkowski's theorem, existence of
  a non-zero lattice point inside a convex symmetric domain of large enough volume.

## TODO

* Calculate the volume of the fundamental domain of a finite index subgroup
* Voronoi diagrams
* See [Pete L. Clark, *Abstract Geometry of Numbers: Linear Forms* (arXiv)](https://arxiv.org/abs/1405.2119)
  for some more ideas.

## References

* [Pete L. Clark, *Geometry of Numbers with Applications to Number Theory*][clark_gon] p.28
-/

namespace MeasureTheory

open ENNReal Module MeasureTheory MeasureTheory.Measure Set Filter

open scoped Pointwise NNReal

variable {E L : Type*} [MeasurableSpace E] {μ : Measure E} {F s : Set E}

theorem exists_pair_mem_lattice_not_disjoint_vadd [AddCommGroup L] [Countable L] [AddAction L E]
    [MeasurableSpace L] [MeasurableVAdd L E] [VAddInvariantMeasure L E μ]
    (fund : IsAddFundamentalDomain L F μ) (hS : NullMeasurableSet s μ) (h : μ F < μ s) :
    ∃ x y : L, x ≠ y ∧ ¬Disjoint (x +ᵥ s) (y +ᵥ s) := by
  contrapose! h
  exact ((fund.measure_eq_tsum _).trans (measure_iUnion₀
    (Pairwise.mono h fun i j hij => (hij.mono inf_le_left inf_le_left).aedisjoint)
      fun _ => (hS.vadd _).inter fund.nullMeasurableSet).symm).trans_le
      (measure_mono <| Set.iUnion_subset fun _ => Set.inter_subset_right)

-- DISSOLVED: exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure

-- DISSOLVED: exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure

end MeasureTheory
