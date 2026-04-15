/-
Extracted from NumberTheory/ClassNumber/AdmissibleAbs.lean
Genuine: 1 | Conflates: 0 | Dissolved: 1 | Infrastructure: 1
-/
import Origin.Core
import Mathlib.Algebra.Algebra.Basic
import Mathlib.NumberTheory.ClassNumber.AdmissibleAbsoluteValue
import Mathlib.Data.Real.Archimedean

/-!
# Admissible absolute value on the integers
This file defines an admissible absolute value `AbsoluteValue.absIsAdmissible`
which we use to show the class number of the ring of integers of a number field
is finite.

## Main results

 * `AbsoluteValue.absIsAdmissible` shows the "standard" absolute value on `ℤ`,
   mapping negative `x` to `-x`, is admissible.
-/

namespace AbsoluteValue

open Int

-- DISSOLVED: exists_partition_int

noncomputable def absIsAdmissible : IsAdmissible AbsoluteValue.abs :=
  { AbsoluteValue.abs_isEuclidean with
    card := fun ε ↦ ⌈1 / ε⌉₊
    exists_partition' := fun n _ hε _ hb ↦ exists_partition_int n hε hb }

noncomputable instance : Inhabited (IsAdmissible AbsoluteValue.abs) :=
  ⟨absIsAdmissible⟩

end AbsoluteValue
