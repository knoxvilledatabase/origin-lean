/-
Extracted from Algebra/Polynomial/Basis.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Basis of a polynomial ring

-/

open Module

universe u

variable (R : Type u) [Semiring R]

namespace Polynomial

def basisMonomials : Basis ℕ R R[X] :=
  Basis.ofRepr (toFinsuppIsoLinear R)
