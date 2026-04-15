/-
Extracted from Order/BoundedOrder/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# ⊤ and ⊥, bounded lattices and variants

This file defines top and bottom elements (greatest and least elements) of a type, the bounded
variants of different kinds of lattices, sets up the typeclass hierarchy between them and provides
instances for `Prop` and `fun`.

## Main declarations

* `<Top/Bot> α`: Typeclasses to declare the `⊤`/`⊥` notation.
* `Order<Top/Bot> α`: Order with a top/bottom element.
* `BoundedOrder α`: Order with a top and bottom element.

-/

assert_not_exists Monotone

universe u v

variable {α : Type u} {β : Type v}

/-! ### Top, bottom element -/

class OrderTop (α : Type u) [LE α] extends Top α where
  /-- `⊤` is the greatest element -/
  le_top : ∀ a : α, a ≤ ⊤
