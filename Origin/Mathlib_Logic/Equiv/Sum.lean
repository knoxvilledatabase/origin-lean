/-
Extracted from Logic/Equiv/Sum.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Equivalence between sum types

In this file we continue the work on equivalences begun in `Mathlib/Logic/Equiv/Defs.lean`, defining

* canonical isomorphisms between various types: e.g.,

  - `Equiv.sumEquivSigmaBool` is the canonical equivalence between the sum of two types `α ⊕ β`
    and the sigma-type `Σ b, bif b then β else α`;

  - `Equiv.prodSumDistrib : α × (β ⊕ γ) ≃ (α × β) ⊕ (α × γ)` shows that type product and type sum
    satisfy the distributive law up to a canonical equivalence;

More definitions of this kind can be found in other files.
E.g., `Mathlib/Algebra/Group/TransferInstance.lean` does it for `Group`,
`Mathlib/Algebra/Module/TransferInstance.lean` does it for `Module`, and similar files exist for
other algebraic type classes.

## Tags

equivalence, congruence, bijective map
-/

universe u v w z

open Function

variable {α α₁ α₂ β β₁ β₂ γ δ : Sort*}

namespace Equiv

open Sum

def psumEquivSum (α β) : α ⊕' β ≃ α ⊕ β where
  toFun s := PSum.casesOn s inl inr
  invFun := Sum.elim PSum.inl PSum.inr
  left_inv s := by cases s <;> rfl
  right_inv s := by cases s <;> rfl
