/-
Extracted from LinearAlgebra/AffineSpace/Matrix.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Matrix results for barycentric co-ordinates

Results about the matrix of barycentric co-ordinates for a family of points in an affine space, with
respect to some affine basis.
-/

open Affine Matrix

open Set

universe u₁ u₂ u₃ u₄

variable {ι : Type u₁} {k : Type u₂} {V : Type u₃} {P : Type u₄}

variable [AddCommGroup V] [AffineSpace V P]

namespace AffineBasis

section Ring

variable [Ring k] [Module k V] (b : AffineBasis ι k P)

noncomputable def toMatrix {ι' : Type*} (q : ι' → P) : Matrix ι' ι k :=
  fun i j => b.coord j (q i)
