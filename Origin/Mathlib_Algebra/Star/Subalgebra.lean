/-
Extracted from Algebra/Star/Subalgebra.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Star subalgebras

A *-subalgebra is a subalgebra of a *-algebra which is closed under *.

The centralizer of a *-closed set is a *-subalgebra.
-/

universe u v

structure StarSubalgebra (R : Type u) (A : Type v) [CommSemiring R] [StarRing R] [Semiring A]
    [StarRing A] [Algebra R A] [StarModule R A] : Type v extends Subalgebra R A where
  /-- The `carrier` is closed under the `star` operation. -/
  star_mem' {a} : a ∈ carrier → star a ∈ carrier

namespace StarSubalgebra

add_decl_doc StarSubalgebra.toSubalgebra

variable {F R A B C : Type*} [CommSemiring R] [StarRing R]

variable [Semiring A] [StarRing A] [Algebra R A] [StarModule R A]

variable [Semiring B] [StarRing B] [Algebra R B] [StarModule R B]

variable [Semiring C] [StarRing C] [Algebra R C] [StarModule R C]

-- INSTANCE (free from Core): setLike

-- INSTANCE (free from Core): :
