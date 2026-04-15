/-
Extracted from Data/Fintype/Pi.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Fintype instances for pi types
-/

assert_not_exists IsOrderedRing MonoidWithZero

open Finset Function

variable {α β : Type*}

namespace Fintype

variable [DecidableEq α] [Fintype α] {γ δ : α → Type*} {s : ∀ a, Finset (γ a)}

def piFinset (t : ∀ a, Finset (δ a)) : Finset (∀ a, δ a) :=
  (Finset.univ.pi t).map ⟨fun f a => f a (mem_univ a), fun _ _ =>
    by simp +contextual [funext_iff]⟩
