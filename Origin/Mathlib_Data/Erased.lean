/-
Extracted from Data/Erased.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# A type for VM-erased data

This file defines a type `Erased α` which is classically isomorphic to `α`,
but erased in the VM. That is, at runtime every value of `Erased α` is
represented as `0`, just like types and proofs.
-/

universe u

def Erased (α : Sort u) : Sort max 1 u :=
  { s : α → Prop // ∃ a, (a = ·) = s }

namespace Erased
