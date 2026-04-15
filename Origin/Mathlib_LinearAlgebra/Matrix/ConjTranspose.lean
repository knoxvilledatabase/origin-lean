/-
Extracted from LinearAlgebra/Matrix/ConjTranspose.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Matrices over star rings.

## Notation

The scope `Matrix` gives the following notation:

* `ᴴ` for `Matrix.conjTranspose`

-/

universe u u' v w

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

namespace Matrix

def conjTranspose [Star α] (M : Matrix m n α) : Matrix n m α :=
  M.transpose.map star
