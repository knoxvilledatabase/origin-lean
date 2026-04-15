/-
Extracted from Data/Finset/Preimage.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Preimage of a `Finset` under an injective map.
-/

assert_not_exists Finset.sum

open Set Function

universe u v w x

variable {α : Type u} {β : Type v} {ι : Sort w} {γ : Type x}

namespace Finset

section Preimage

noncomputable def preimage (s : Finset β) (f : α → β) (hf : Set.InjOn f (f ⁻¹' ↑s)) : Finset α :=
  (s.finite_toSet.preimage hf).toFinset
