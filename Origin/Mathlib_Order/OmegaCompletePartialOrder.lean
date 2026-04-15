/-
Extracted from Order/OmegaCompletePartialOrder.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Omega Complete Partial Orders

An omega-complete partial order is a partial order with a supremum
operation on increasing sequences indexed by natural numbers (which we
call `ωSup`). In this sense, it is strictly weaker than join complete
semi-lattices as only ω-sized totally ordered sets have a supremum.

The concept of an omega-complete partial order (ωCPO) is useful for the
formalization of the semantics of programming languages. Its notion of
supremum helps define the meaning of recursive procedures.

## Main definitions

* class `OmegaCompletePartialOrder`
* `ite`, `map`, `bind`, `seq` as continuous morphisms

## Instances of `OmegaCompletePartialOrder`

* `Part`
* every `CompleteLattice`
* pi-types
* product types
* `OrderHom`
* `ContinuousHom` (with notation →𝒄)
  * an instance of `OmegaCompletePartialOrder (α →𝒄 β)`
* `ContinuousHom.ofFun`
* `ContinuousHom.ofMono`
* continuous functions:
  * `id`
  * `ite`
  * `const`
  * `Part.bind`
  * `Part.map`
  * `Part.seq`

## References

* [Chain-complete posets and directed sets with applications][markowsky1976]
* [Recursive definitions of partial functions and their computations][cadiou1972]
* [Semantics of Programming Languages: Structures and Techniques][gunter1992]
-/

assert_not_exists IsOrderedMonoid

universe u v

variable {ι : Sort*} {α β γ δ : Type*}

namespace OmegaCompletePartialOrder

structure Chain (α : Type u) [Preorder α] extends ℕ →o α

namespace Chain

variable [Preorder α] [Preorder β] [Preorder γ]

-- INSTANCE (free from Core): :

initialize_simps_projections Chain (toFun → apply)

-- INSTANCE (free from Core): :
