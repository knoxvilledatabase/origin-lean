/-
Extracted from Logic/Function/FromTypes.lean
Genuine: 3 of 5 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-! # Function types of a given heterogeneous arity

This provides `Function.FromTypes`, such that `FromTypes ![α, β] τ = α → β → τ`.
Note that it is often preferable to use `((i : Fin n) → p i) → τ` in place of `FromTypes p τ`.

## Main definitions

* `Function.FromTypes p τ`: `n`-ary function `p 0 → p 1 → ... → p (n - 1) → β`.
-/

universe u

namespace Function

open Matrix (vecCons vecHead vecTail vecEmpty)

set_option linter.style.whitespace false in -- manual alignment is not recognised

def FromTypes : {n : ℕ} → (Fin n → Type u) → Type u → Type u
  | 0    , _, τ => τ
  | n + 1, p, τ => vecHead p → @FromTypes n (vecTail p) τ

theorem fromTypes_nil (τ : Type u) : FromTypes ![] τ = τ := fromTypes_zero ![] τ

theorem fromTypes_cons {n} (α : Type u) (p : Fin n → Type u) (τ : Type u) :
    FromTypes (vecCons α p) τ = (α → FromTypes p τ) := fromTypes_succ _ τ
