/-
Extracted from NumberTheory/ClassNumber/FunctionField.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Class numbers of function fields

This file defines the class number of a function field as the (finite) cardinality of
the class group of its ring of integers. It also proves some elementary results
on the class number.

## Main definitions
- `FunctionField.classNumber`: the class number of a function field is the (finite)
  cardinality of the class group of its ring of integers
-/

namespace FunctionField

open scoped Polynomial

variable (Fq F : Type*) [Field Fq] [Fintype Fq] [Field F]

variable [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]

variable [IsScalarTower Fq[X] (RatFunc Fq) F]

variable [FunctionField Fq F] [Algebra.IsSeparable (RatFunc Fq) F]

namespace RingOfIntegers

open FunctionField

open scoped Classical in

-- INSTANCE (free from Core): :

end RingOfIntegers

noncomputable def classNumber : ℕ :=
  Fintype.card (ClassGroup (ringOfIntegers Fq F))

theorem classNumber_eq_one_iff :
    classNumber Fq F = 1 ↔ IsPrincipalIdealRing (ringOfIntegers Fq F) :=
  card_classGroup_eq_one_iff

end FunctionField
