/-
Extracted from FieldTheory/Normal/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Normal field extensions

In this file we prove that for a finite extension, being normal
is the same as being a splitting field (`Normal.of_isSplittingField` and
`Normal.exists_isSplittingField`).

## Additional Results

* `Algebra.IsQuadraticExtension.normal`: the instance that a quadratic extension, given as a class
  `Algebra.IsQuadraticExtension`, is normal.

-/

noncomputable section

open Polynomial IsScalarTower

variable (F K : Type*) [Field F] [Field K] [Algebra F K]

theorem Normal.exists_isSplittingField [h : Normal F K] [FiniteDimensional F K] :
    ∃ p : F[X], IsSplittingField F K p := by
  classical
  let s := Module.Basis.ofVectorSpace F K
  refine
    ⟨∏ x, minpoly F (s x), Polynomial.map_prod (algebraMap F K) _ _ ▸
      Splits.prod fun x _ => h.splits (s x), Subalgebra.toSubmodule.injective ?_⟩
  rw [Algebra.top_toSubmodule, eq_top_iff, ← s.span_eq, Submodule.span_le, Set.range_subset_iff]
  refine fun x =>
    Algebra.subset_adjoin
      (Multiset.mem_toFinset.mpr <|
        (mem_roots <|
              mt (Polynomial.map_eq_zero <| algebraMap F K).1 <|
                Finset.prod_ne_zero_iff.2 fun x _ => ?_).2 ?_)
  · exact minpoly.ne_zero (h.isIntegral (s x))
  rw [IsRoot.def, eval_map_algebraMap, map_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ _) (minpoly.aeval _ _)

section NormalTower

variable (E : Type*) [Field E] [Algebra F E] [Algebra K E] [IsScalarTower F K E]

variable {E F}

open IntermediateField
