/-
Extracted from Topology/Order/Hom/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Continuous order homomorphisms

This file defines continuous order homomorphisms, that is maps which are both continuous and
monotone. They are also called Priestley homomorphisms because they are the morphisms of the
category of Priestley spaces.

We use the `DFunLike` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.

## Types of morphisms

* `ContinuousOrderHom`: Continuous monotone functions, aka Priestley homomorphisms.

## Typeclasses

* `ContinuousOrderHomClass`
-/

open Function

variable {F α β γ δ : Type*}

structure ContinuousOrderHom (α β : Type*) [Preorder α] [Preorder β] [TopologicalSpace α]
  [TopologicalSpace β] extends OrderHom α β where
  continuous_toFun : Continuous toFun
