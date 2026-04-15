/-
Extracted from Analysis/CStarAlgebra/CStarMatrix.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Matrices with entries in a C⋆-algebra

This file creates a type copy of `Matrix m n A` called `CStarMatrix m n A` meant for matrices with
entries in a C⋆-algebra `A`. Its action on `C⋆ᵐᵒᵈ (n → A)` (via `Matrix.mulVec`) gives
it the operator norm, and this norm makes `CStarMatrix n n A` a C⋆-algebra.

## Main declarations

+ `CStarMatrix m n A`: the type copy
+ `CStarMatrix.instNonUnitalCStarAlgebra`: square matrices with entries in a non-unital C⋆-algebra
    form a non-unital C⋆-algebra
+ `CStarMatrix.instCStarAlgebra`: square matrices with entries in a unital C⋆-algebra form a
    unital C⋆-algebra

## Implementation notes

The norm on this type induces the product uniformity and bornology, but these are not defeq to
`Pi.uniformSpace` and `Pi.instBornology`. Hence, we prove the equality to the Pi instances and
replace the uniformity and bornology by the Pi ones when registering the
`NormedAddCommGroup (CStarMatrix m n A)` instance. See the docstring of the `TopologyAux` section
below for more details.
-/

open scoped ComplexOrder Topology Uniformity Bornology Matrix NNReal InnerProductSpace

  WithCStarModule

def CStarMatrix (m : Type*) (n : Type*) (A : Type*) := Matrix m n A

namespace CStarMatrix

variable {m n R S A B : Type*}

section basic

variable (m n A) in

def ofMatrix {m n A : Type*} : Matrix m n A ≃ CStarMatrix m n A := Equiv.refl _
