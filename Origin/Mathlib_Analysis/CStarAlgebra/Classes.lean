/-
Extracted from Analysis/CStarAlgebra/Classes.lean
Genuine: 4 of 27 | Dissolved: 0 | Infrastructure: 23
-/
import Origin.Core

/-! # Classes of C⋆-algebras

This file defines classes for complex C⋆-algebras. These are (unital or non-unital, commutative or
noncommutative) Banach algebra over `ℂ` with an antimultiplicative conjugate-linear involution
(`star`) satisfying the C⋆-identity `∥star x * x∥ = ∥x∥ ^ 2`.

## Notes

These classes are not defined in `Mathlib/Analysis/CStarAlgebra/Basic.lean` because they require
heavier imports.

-/

noncomputable section

class NonUnitalCStarAlgebra (A : Type*) extends NonUnitalNormedRing A, StarRing A, CompleteSpace A,
    CStarRing A, NormedSpace ℂ A, IsScalarTower ℂ A A, SMulCommClass ℂ A A, StarModule ℂ A where

class NonUnitalCommCStarAlgebra (A : Type*) extends
    NonUnitalNormedCommRing A, NonUnitalCStarAlgebra A

class CStarAlgebra (A : Type*) extends NormedRing A, StarRing A, CompleteSpace A, CStarRing A,
    NormedAlgebra ℂ A, StarModule ℂ A where

class CommCStarAlgebra (A : Type*) extends NormedCommRing A, CStarAlgebra A

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): StarSubalgebra.cstarAlgebra

-- INSTANCE (free from Core): StarSubalgebra.commCStarAlgebra

-- INSTANCE (free from Core): NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

-- INSTANCE (free from Core): NonUnitalStarSubalgebra.nonUnitalCommCStarAlgebra

-- INSTANCE (free from Core): :

section Elemental

variable {A : Type*}

-- INSTANCE (free from Core): [CStarAlgebra

-- INSTANCE (free from Core): [NonUnitalCStarAlgebra

-- INSTANCE (free from Core): [CStarAlgebra

-- INSTANCE (free from Core): [NonUnitalCStarAlgebra

end Elemental

section Pi

variable {ι : Type*} {A : ι → Type*} [Fintype ι]

-- INSTANCE (free from Core): [(i

-- INSTANCE (free from Core): [(i

-- INSTANCE (free from Core): [(i

-- INSTANCE (free from Core): [(i

end Pi

section Prod

variable {A B : Type*}

-- INSTANCE (free from Core): [NonUnitalCStarAlgebra

-- INSTANCE (free from Core): [NonUnitalCommCStarAlgebra

-- INSTANCE (free from Core): [CStarAlgebra

-- INSTANCE (free from Core): [CommCStarAlgebra

end Prod

namespace MulOpposite

variable {A : Type*}

-- INSTANCE (free from Core): [NonUnitalCStarAlgebra

-- INSTANCE (free from Core): [NonUnitalCommCStarAlgebra

-- INSTANCE (free from Core): [CStarAlgebra

-- INSTANCE (free from Core): [CommCStarAlgebra

end MulOpposite
