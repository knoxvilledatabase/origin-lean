/-
Extracted from Logic/Encodable/Pi.lean
Genuine: 2 of 7 | Dissolved: 0 | Infrastructure: 5
-/
import Origin.Core

/-!
# Encodability of Pi types

This file provides instances of `Encodable` for types of vectors and (dependent) functions:

* `Encodable.List.Vector.encodable`: vectors of length `n` (represented by lists) are encodable
* `Encodable.finArrow`: vectors of length `n` (represented by `Fin`-indexed functions) are encodable
* `Encodable.fintypeArrow`, `Encodable.fintypePi`: (dependent) functions with
  finite domain and countable codomain are encodable
-/

open List (Vector)

open Nat List

namespace Encodable

variable {α : Type*}

-- INSTANCE (free from Core): List.Vector.encodable

-- INSTANCE (free from Core): List.Vector.countable

-- INSTANCE (free from Core): finArrow

-- INSTANCE (free from Core): finPi

def fintypeArrow (α : Type*) (β : Type*) [DecidableEq α] [Fintype α] [Encodable β] :
    Trunc (Encodable (α → β)) :=
  (Fintype.truncEquivFin α).map fun f =>
    Encodable.ofEquiv (Fin (Fintype.card α) → β) <| Equiv.arrowCongr f (Equiv.refl _)

def fintypePi (α : Type*) (π : α → Type*) [DecidableEq α] [Fintype α] [∀ a, Encodable (π a)] :
    Trunc (Encodable (∀ a, π a)) :=
  (Fintype.truncEncodable α).bind fun a =>
    (@fintypeArrow α (Σ a, π a) _ _ (@Sigma.encodable _ _ a _)).bind fun f =>
      Trunc.mk <|
        @Encodable.ofEquiv _ _ (@Subtype.encodable _ _ f _)
          (Equiv.piEquivSubtypeSigma α π)

-- INSTANCE (free from Core): fintypeArrowOfEncodable

end Encodable
