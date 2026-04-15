/-
Extracted from LinearAlgebra/Basis/MulOpposite.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Basis of an opposite space

This file defines the basis of an opposite space and shows
that the opposite space is finite-dimensional and free when the original space is.
-/

open Module MulOpposite

variable {R H : Type*}

namespace Module.Basis

variable {ι : Type*} [Semiring R] [AddCommMonoid H] [Module R H]

noncomputable def mulOpposite (b : Basis ι R H) : Basis ι R Hᵐᵒᵖ :=
  b.map (opLinearEquiv R)
