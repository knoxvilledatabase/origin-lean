/-
Extracted from Topology/Algebra/Ring/Basic.lean
Genuine: 5 of 5 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Topological (semi)rings

A topological (semi)ring is a (semi)ring equipped with a topology such that all operations are
continuous. Besides this definition, this file proves that the topological closure of a subring
(resp. an ideal) is a subring (resp. an ideal) and defines products and quotients
of topological (semi)rings.

## Main Results

- `Subring.topologicalClosure`/`Subsemiring.topologicalClosure`: the topological closure of a
  `Subring`/`Subsemiring` is itself a `Sub(semi)ring`.
- The product of two topological (semi)rings is a topological (semi)ring.
- The indexed product of topological (semi)rings is a topological (semi)ring.
-/

assert_not_exists Cardinal

open Set Filter TopologicalSpace Function Topology Filter

section IsTopologicalSemiring

variable (R : Type*)

class IsTopologicalSemiring [TopologicalSpace R] [NonUnitalNonAssocSemiring R] : Prop
    extends ContinuousAdd R, ContinuousMul R

class IsTopologicalRing [TopologicalSpace R] [NonUnitalNonAssocRing R] : Prop
    extends IsTopologicalSemiring R, ContinuousNeg R

class IsSemitopologicalSemiring (R : Type*) [TopologicalSpace R] [NonUnitalNonAssocSemiring R]
  extends ContinuousAdd R, SeparatelyContinuousMul R

class IsSemitopologicalRing (R : Type*) [TopologicalSpace R] [NonUnitalNonAssocRing R]
  extends IsSemitopologicalSemiring R, ContinuousNeg R

variable {R}

theorem IsSemitopologicalSemiring.continuousNeg_of_mul [TopologicalSpace R] [NonAssocRing R]
    [SeparatelyContinuousMul R] : ContinuousNeg R where
  continuous_neg := by simpa using continuous_id.const_mul (-1 : R)
