/-
Extracted from Topology/Algebra/NonUnitalAlgebra.lean
Genuine: 4 of 6 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Non-unital topological (sub)algebras

A non-unital topological algebra over a topological semiring `R` is a topological (non-unital)
semiring with a compatible continuous scalar multiplication by elements of `R`. We reuse
typeclass `ContinuousSMul` to express the latter condition.

## Results

Any non-unital subalgebra of a non-unital topological algebra is itself a non-unital
topological algebra, and its closure is again a non-unital subalgebra.

-/

namespace NonUnitalSubalgebra

section Semiring

variable {R A B : Type*} [CommSemiring R] [TopologicalSpace A]

variable [NonUnitalSemiring A] [Module R A]

variable [ContinuousConstSMul R A]

-- INSTANCE (free from Core): instIsTopologicalSemiring

-- INSTANCE (free from Core): instIsSemitopologicalSemiring

variable [IsSemitopologicalSemiring A]

def topologicalClosure (s : NonUnitalSubalgebra R A) : NonUnitalSubalgebra R A :=
  { s.toNonUnitalSubsemiring.topologicalClosure, s.toSubmodule.topologicalClosure with
    carrier := _root_.closure (s : Set A) }

theorem le_topologicalClosure (s : NonUnitalSubalgebra R A) : s ≤ s.topologicalClosure :=
  subset_closure

theorem isClosed_topologicalClosure (s : NonUnitalSubalgebra R A) :
    IsClosed (s.topologicalClosure : Set A) := isClosed_closure

theorem topologicalClosure_minimal {s t : NonUnitalSubalgebra R A}
    (h : s ≤ t) (ht : IsClosed (t : Set A)) : s.topologicalClosure ≤ t :=
  closure_minimal h ht
