/-
Extracted from Data/WSeq/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Partially defined possibly infinite lists

This file provides a `WSeq α` type representing partially defined possibly infinite lists
(referred here as weak sequences).
-/

namespace Stream'

open Function

universe u v w

def WSeq (α) :=
  Seq (Option α)

namespace WSeq

variable {α : Type u} {β : Type v} {γ : Type w}
