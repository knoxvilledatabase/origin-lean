/-
Extracted from Order/PFilter.lean
Genuine: 8 of 11 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Order filters

## Main definitions

Throughout this file, `P` is at least a preorder, but some sections require more structure,
such as a bottom element, a top element, or a join-semilattice structure.

- `Order.PFilter P`: The type of nonempty, downward directed, upward closed subsets of `P`.
               This is dual to `Order.Ideal`, so it simply wraps `Order.Ideal Pᵒᵈ`.
- `Order.IsPFilter P`: a predicate for when a `Set P` is a filter.

Note the relation between `Order/Filter` and `Order/PFilter`: for any type `α`,
`Filter α` represents the same mathematical object as `PFilter (Set α)`.

## References

- <https://en.wikipedia.org/wiki/Filter_(mathematics)>

## Tags

pfilter, filter, ideal, dual

-/

open OrderDual

namespace Order

structure PFilter (P : Type*) [Preorder P] where
  dual : Ideal Pᵒᵈ

variable {P : Type*}

def IsPFilter [Preorder P] (F : Set P) : Prop :=
  IsIdeal (OrderDual.ofDual ⁻¹' F)

theorem IsPFilter.of_def [Preorder P] {F : Set P} (nonempty : F.Nonempty)
    (directed : DirectedOn (· ≥ ·) F) (mem_of_le : ∀ {x y : P}, x ≤ y → x ∈ F → y ∈ F) :
    IsPFilter F :=
  ⟨fun _ _ _ _ => mem_of_le ‹_› ‹_›, nonempty, directed⟩

def IsPFilter.toPFilter [Preorder P] {F : Set P} (h : IsPFilter F) : PFilter P :=
  ⟨h.toIdeal⟩

namespace PFilter

section Preorder

variable [Preorder P] {x y : P} (F s t : PFilter P)

-- INSTANCE (free from Core): [Inhabited

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

theorem isPFilter : IsPFilter (F : Set P) := F.dual.isIdeal

protected theorem nonempty : (F : Set P).Nonempty := F.dual.nonempty

theorem directed : DirectedOn (· ≥ ·) (F : Set P) := F.dual.directed

theorem mem_of_le {F : PFilter P} : x ≤ y → x ∈ F → y ∈ F := fun h => F.dual.lower h
