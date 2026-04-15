/-
Extracted from Algebra/Category/CommAlgCat/Monoidal.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The co-Cartesian monoidal category structure on commutative `R`-algebras

This file provides the co-Cartesian-monoidal category structure on `CommAlgCat R` constructed
explicitly using the tensor product.
-/

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Limits TensorProduct Opposite

open Algebra.TensorProduct

open Algebra.TensorProduct (lid rid assoc comm)

noncomputable section

namespace CommAlgCat

universe u v

variable {R : Type u} [CommRing R] {A B C D : CommAlgCat.{u} R}

variable (A B)

def binaryCofan : BinaryCofan A B := .mk (ofHom includeLeft) (ofHom <| includeRight (A := A))
