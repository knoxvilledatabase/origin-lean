/-
Extracted from Analysis/InnerProductSpace/GramMatrix.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! # Gram Matrices

This file defines Gram matrices and proves their positive semidefiniteness.
Results require `RCLike 𝕜`.

## Main definition

* `Matrix.gram` : the `Matrix n n 𝕜` with `⟪v i, v j⟫` at `i j : n`, where `v : n → E` for an
  `Inner 𝕜 E`.

## Main results

* `Matrix.posSemidef_gram`: Gram matrices are positive semidefinite.
* `Matrix.posDef_gram_iff_linearIndependent`: Linear independence of `v` is
  equivalent to positive definiteness of `gram 𝕜 v`.
-/

open RCLike Real Matrix

open scoped InnerProductSpace ComplexOrder ComplexConjugate

variable {E n α 𝕜 : Type*}

namespace Matrix

def gram (𝕜 : Type*) [Inner 𝕜 E] (v : n → E) : Matrix n n 𝕜 := of fun i j ↦ ⟪v i, v j⟫_𝕜
