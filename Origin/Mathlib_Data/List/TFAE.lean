/-
Extracted from Data/List/TFAE.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The Following Are Equivalent

This file allows to state that all propositions in a list are equivalent. It is used by
`Mathlib/Tactic/Tfae.lean`.
`TFAE l` means `∀ x ∈ l, ∀ y ∈ l, x ↔ y`. This is equivalent to `Pairwise (↔) l`.
-/

namespace List

def TFAE (l : List Prop) : Prop :=
  ∀ x ∈ l, ∀ y ∈ l, x ↔ y

theorem tfae_nil : TFAE [] :=
  forall_mem_nil _
