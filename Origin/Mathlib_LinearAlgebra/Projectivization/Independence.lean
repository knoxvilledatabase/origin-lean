/-
Extracted from LinearAlgebra/Projectivization/Independence.lean
Genuine: 5 of 7 | Dissolved: 2 | Infrastructure: 0
-/
import Origin.Core

/-!
# Independence in Projective Space

In this file we define independence and dependence of families of elements in projective space.

## Implementation Details

We use an inductive definition to define the independence of points in projective
space, where the only constructor assumes an independent family of vectors from the
ambient vector space. Similarly for the definition of dependence.

## Results

- A family of elements is dependent if and only if it is not independent.
- Two elements are dependent if and only if they are equal.

## Future Work

- Define collinearity in projective space.
- Prove the axioms of a projective geometry are satisfied by the dependence relation.
- Define projective linear subspaces.
-/

open scoped LinearAlgebra.Projectivization

variable {ι K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] {f : ι → ℙ K V}

namespace Projectivization

-- DISSOLVED: Independent

theorem independent_iff : Independent f ↔ LinearIndependent K (Projectivization.rep ∘ f) := by
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨ff, hff, hh⟩
    choose a ha using fun i : ι => exists_smul_eq_mk_rep K (ff i) (hff i)
    convert hh.units_smul a
    ext i
    exact (ha i).symm
  · convert Independent.mk _ _ h
    · simp only [mk_rep, Function.comp_apply]
    · intro i
      apply rep_nonzero

theorem independent_iff_iSupIndep : Independent f ↔ iSupIndep fun i => (f i).submodule := by
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨f, hf, hi⟩
    simp only [submodule_mk]
    exact (iSupIndep_iff_linearIndependent_of_ne_zero (R := K) hf).mpr hi
  · rw [independent_iff]
    refine h.linearIndependent (Projectivization.submodule ∘ f) (fun i => ?_) fun i => ?_
    · simpa only [Function.comp_apply, submodule_eq] using Submodule.mem_span_singleton_self _
    · exact rep_nonzero (f i)

-- DISSOLVED: Dependent

theorem dependent_iff : Dependent f ↔ ¬LinearIndependent K (Projectivization.rep ∘ f) := by
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨ff, hff, hh1⟩
    contrapose hh1
    choose a ha using fun i : ι => exists_smul_eq_mk_rep K (ff i) (hff i)
    convert hh1.units_smul a⁻¹
    ext i
    simp only [← ha, inv_smul_smul, Pi.smul_apply', Pi.inv_apply, Function.comp_apply]
  · convert Dependent.mk _ _ h
    · simp only [mk_rep, Function.comp_apply]
    · exact fun i => rep_nonzero (f i)

theorem dependent_iff_not_independent : Dependent f ↔ ¬Independent f := by
  rw [dependent_iff, independent_iff]

theorem independent_iff_not_dependent : Independent f ↔ ¬Dependent f := by
  rw [dependent_iff_not_independent, Classical.not_not]
