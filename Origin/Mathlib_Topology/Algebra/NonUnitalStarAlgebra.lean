/-
Extracted from Topology/Algebra/NonUnitalStarAlgebra.lean
Genuine: 4 of 6 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Non-unital topological star (sub)algebras

A non-unital topological star algebra over a topological semiring `R` is a topological
(non-unital) semiring with a compatible continuous scalar multiplication by elements
of `R` and a continuous `star` operation. We reuse typeclasses `ContinuousSMul` and
`ContinuousStar` to express the latter two conditions.

## Results

Any non-unital star subalgebra of a non-unital topological star algebra is itself a
non-unital topological star algebra, and its closure is again a non-unital star subalgebra.

-/

namespace NonUnitalStarSubalgebra

section Semiring

variable {R A B : Type*} [CommSemiring R] [TopologicalSpace A] [Star A]

variable [NonUnitalSemiring A] [Module R A] [ContinuousStar A]

variable [ContinuousConstSMul R A]

-- INSTANCE (free from Core): instIsTopologicalSemiring

-- INSTANCE (free from Core): instIsSemitopologicalSemiring

variable [IsSemitopologicalSemiring A]

def topologicalClosure (s : NonUnitalStarSubalgebra R A) : NonUnitalStarSubalgebra R A :=
  { s.toNonUnitalSubalgebra.topologicalClosure with
    star_mem' := fun h ↦ map_mem_closure continuous_star h fun _ ↦ star_mem
    carrier := _root_.closure (s : Set A) }

theorem le_topologicalClosure (s : NonUnitalStarSubalgebra R A) : s ≤ s.topologicalClosure :=
  subset_closure

theorem isClosed_topologicalClosure (s : NonUnitalStarSubalgebra R A) :
    IsClosed (s.topologicalClosure : Set A) := isClosed_closure

theorem topologicalClosure_minimal (s : NonUnitalStarSubalgebra R A)
    {t : NonUnitalStarSubalgebra R A} (h : s ≤ t) (ht : IsClosed (t : Set A)) :
    s.topologicalClosure ≤ t :=
  closure_minimal h ht
