/-
Extracted from LinearAlgebra/AffineSpace/Simplex/Basic.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Simplex in affine space

This file defines n-dimensional simplices in affine space.

## Main definitions

* `Simplex` is a bundled type with collection of `n + 1` points in affine space that are affinely
  independent, where `n` is the dimension of the simplex.

* `Triangle` is a simplex with three points, defined as an abbreviation for simplex with `n = 2`.

* `face` is a simplex with a subset of the points of the original simplex.

## References

* https://en.wikipedia.org/wiki/Simplex

-/

noncomputable section

open Finset Function Module

open scoped Affine

namespace Affine

variable (k : Type*) {V V₂ V₃ : Type*} (P P₂ P₃ : Type*)

variable [Ring k] [AddCommGroup V] [AddCommGroup V₂] [AddCommGroup V₃]

variable [Module k V] [Module k V₂] [Module k V₃]

variable [AffineSpace V P] [AffineSpace V₂ P₂] [AffineSpace V₃ P₃]

structure Simplex (n : ℕ) where
  points : Fin (n + 1) → P
  independent : AffineIndependent k points

abbrev Triangle :=
  Simplex k P 2

namespace Simplex

variable {P P₂ P₃}

def mkOfPoint (p : P) : Simplex k P 0 :=
  have : Subsingleton (Fin (1 + 0)) := by rw [add_zero]; infer_instance
  ⟨fun _ => p, affineIndependent_of_subsingleton k _⟩
