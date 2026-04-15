/-
Extracted from Logic/Small/Basic.lean
Genuine: 2 of 11 | Dissolved: 0 | Infrastructure: 9
-/
import Origin.Core

/-!
# Instances and theorems for `Small`.

In particular we prove `small_of_injective` and `small_of_surjective`.
-/

assert_not_exists Countable

universe u w v v'

-- INSTANCE (free from Core): small_subtype

theorem small_of_injective {α : Type v} {β : Type w} [Small.{u} β] {f : α → β}
    (hf : Function.Injective f) : Small.{u} α :=
  small_map (Equiv.ofInjective f hf)

theorem small_of_surjective {α : Type v} {β : Type w} [Small.{u} α] {f : α → β}
    (hf : Function.Surjective f) : Small.{u} β :=
  small_of_injective (Function.injective_surjInv hf)

-- INSTANCE (free from Core): (priority

/-!
We don't define `Countable.toSmall` in this file, to keep imports to `Logic` to a minimum.
-/

-- INSTANCE (free from Core): small_Pi

-- INSTANCE (free from Core): small_prod

-- INSTANCE (free from Core): small_sum

-- INSTANCE (free from Core): small_set

-- INSTANCE (free from Core): small_quot

-- INSTANCE (free from Core): small_quotient
