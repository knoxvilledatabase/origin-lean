/-
Extracted from ModelTheory/Order.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Ordered First-Ordered Structures

This file defines ordered first-order languages and structures, as well as their theories.

## Main Definitions

- `FirstOrder.Language.order` is the language consisting of a single relation representing `≤`.
- `FirstOrder.Language.IsOrdered` points out a specific symbol in a language as representing `≤`.
- `FirstOrder.Language.OrderedStructure` indicates that the `≤` symbol in an ordered language
  is interpreted as the actual relation `≤` in a particular structure.
- `FirstOrder.Language.linearOrderTheory` and similar define the theories of preorders,
  partial orders, and linear orders.
- `FirstOrder.Language.dlo` defines the theory of dense linear orders without endpoints, a
  particularly useful example in model theory.
- `FirstOrder.Language.orderStructure` is the structure on an ordered type, assigning the symbol
  representing `≤` to the actual relation `≤`.
- Conversely, `FirstOrder.Language.LEOfStructure`, `FirstOrder.Language.preorderOfModels`,
  `FirstOrder.Language.partialOrderOfModels`, and `FirstOrder.Language.linearOrderOfModels`
  are the orders induced by first-order structures modelling the relevant theory.

## Main Results

- `PartialOrder`s model the theory of partial orders, `LinearOrder`s model the theory of
  linear orders, and dense linear orders without endpoints model `Language.dlo`.
- Under `L.orderedStructure` assumptions, elements of any `L.HomClass M N` are monotone, and
  strictly monotone if injective.
- Under `Language.order.orderedStructure` assumptions, any `OrderHomClass` has an instance of
  `L.HomClass M N`, while `M ↪o N` and any `OrderIsoClass` have an instance of
  `L.StrongHomClass M N`.
- `FirstOrder.Language.isFraisseLimit_of_countable_nonempty_dlo` shows that any countable nonempty
  model of the theory of linear orders is a Fraïssé limit of the class of finite models of the
  theory of linear orders.
- `FirstOrder.Language.isFraisse_finite_linear_order` shows that the class of finite models of the
  theory of linear orders is Fraïssé.
- `FirstOrder.Language.aleph0_categorical_dlo` shows that the theory of dense linear orders is
  `ℵ₀`-categorical, and thus complete.

-/

universe u v w w'

namespace FirstOrder

namespace Language

open FirstOrder Structure

variable {L : Language.{u, v}} {α : Type w} {M : Type w'} {n : ℕ}

inductive orderRel : ℕ → Type
  | le : orderRel 2
  deriving DecidableEq

protected def order : Language := ⟨fun _ => Empty, orderRel⟩
  deriving IsRelational

namespace order
