/-
Extracted from Topology/Order/Hom/Esakia.lean
Genuine: 4 of 11 | Dissolved: 0 | Infrastructure: 7
-/
import Origin.Core

/-!
# Esakia morphisms

This file defines pseudo-epimorphisms and Esakia morphisms.

We use the `DFunLike` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.

## Types of morphisms

* `PseudoEpimorphism`: Pseudo-epimorphisms. Maps `f` such that `f a ≤ b` implies the existence of
  `a'` such that `a ≤ a'` and `f a' = b`.
* `EsakiaHom`: Esakia morphisms. Continuous pseudo-epimorphisms.

## Typeclasses

* `PseudoEpimorphismClass`
* `EsakiaHomClass`

## References

* [Wikipedia, *Esakia space*](https://en.wikipedia.org/wiki/Esakia_space)
-/

open Function

variable {F α β γ δ : Type*}

structure PseudoEpimorphism (α β : Type*) [Preorder α] [Preorder β] extends α →o β where
  exists_map_eq_of_map_le' ⦃a : α⦄ ⦃b : β⦄ : toFun a ≤ b → ∃ c, a ≤ c ∧ toFun c = b

structure EsakiaHom (α β : Type*) [TopologicalSpace α] [Preorder α] [TopologicalSpace β]
  [Preorder β] extends α →Co β where
  exists_map_eq_of_map_le' ⦃a : α⦄ ⦃b : β⦄ : toFun a ≤ b → ∃ c, a ≤ c ∧ toFun c = b

class PseudoEpimorphismClass (F : Type*) (α β : outParam Type*)
    [Preorder α] [Preorder β] [FunLike F α β] : Prop
    extends OrderHomClass F α β where
  exists_map_eq_of_map_le (f : F) ⦃a : α⦄ ⦃b : β⦄ : f a ≤ b → ∃ c, a ≤ c ∧ f c = b

class EsakiaHomClass (F : Type*) (α β : outParam Type*) [TopologicalSpace α] [Preorder α]
    [TopologicalSpace β] [Preorder β] [FunLike F α β] : Prop
    extends ContinuousOrderHomClass F α β where
  exists_map_eq_of_map_le (f : F) ⦃a : α⦄ ⦃b : β⦄ : f a ≤ b → ∃ c, a ≤ c ∧ f c = b

end

export PseudoEpimorphismClass (exists_map_eq_of_map_le)

section Hom

variable [FunLike F α β]

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): [Preorder

-- INSTANCE (free from Core): [TopologicalSpace

end Hom

-- INSTANCE (free from Core): (priority

/-! ### Pseudo-epimorphisms -/

namespace PseudoEpimorphism

variable [Preorder α] [Preorder β] [Preorder γ] [Preorder δ]

-- INSTANCE (free from Core): instFunLike

-- INSTANCE (free from Core): :
