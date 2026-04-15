/-
Extracted from Algebra/Homology/EulerCharacteristic.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Euler characteristic of homological complexes

The Euler characteristic is defined using the `ComplexShape.EulerCharSigns` typeclass,
which provides the alternating signs for each index. This allows the definition to work
uniformly for chain complexes, cochain complexes, and complexes with other index types.

The definitions work on graded objects, with the homological complex versions
defined as abbreviations that apply the graded object versions to `C.X` and `C.homology`.

## Junk values

These definitions may have junk values from `finsum` (0 for infinite support) and
`Module.finrank` (0 for modules not free of finite rank).

## Main definitions

* `ComplexShape.EulerCharSigns`: Typeclass providing alternating signs for Euler characteristic
* `GradedObject.eulerChar`: The Euler characteristic of a graded object using `finsum`
* `GradedObject.finrankSupport`: Indices where `Module.finrank` is nonzero
* `HomologicalComplex.eulerChar`: The Euler characteristic using `finsum`
* `HomologicalComplex.homologyEulerChar`: The homological Euler characteristic using `finsum`

## Main results

* `GradedObject.eulerChar_eq_sum_finSet_of_finrankSupport_subset`: The `finsum` equals the
  finite sum when the graded object has finite support contained in the given set
* `HomologicalComplex.eulerChar_eq_sum_finSet_of_finrankSupport_subset`: The `finsum` equals
  the finite sum when the complex has finite support contained in the given set
* `HomologicalComplex.homologyEulerChar_eq_sum_finSet_of_finrankSupport_subset`: The `finsum`
  homological Euler characteristic equals the finite sum when homology has finite support

-/

namespace ComplexShape

variable {ι : Type*} (c : ComplexShape ι)

class EulerCharSigns where
  /-- The sign for each index -/
  χ : ι → ℤˣ
  /-- Signs alternate along relations in the complex shape -/
  χ_next {i j : ι} (h : c.Rel i j) : χ j = - χ i

variable [c.EulerCharSigns]

abbrev χ : ι → ℤˣ := EulerCharSigns.χ c

lemma χ_next {i j : ι} (h : c.Rel i j) : c.χ j = - c.χ i := EulerCharSigns.χ_next h

lemma χ_prev {i j : ι} (h : c.Rel i j) : c.χ i = - c.χ j := by simp [c.χ_next h]
