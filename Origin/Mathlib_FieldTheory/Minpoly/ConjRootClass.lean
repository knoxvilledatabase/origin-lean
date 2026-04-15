/-
Extracted from FieldTheory/Minpoly/ConjRootClass.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Conjugate root classes

In this file, we define the `ConjRootClass` of a field extension `L / K` as the quotient of `L` by
the relation `IsConjRoot K`.
-/

variable (K L S : Type*) [Field K] [Field L] [Field S]

variable [Algebra K L] [Algebra K S] [Algebra L S] [IsScalarTower K L S]

def ConjRootClass := Quotient (α := L) (IsConjRoot.setoid K L)

namespace ConjRootClass

variable {L}

def mk (x : L) : ConjRootClass K L :=
  ⟦x⟧
