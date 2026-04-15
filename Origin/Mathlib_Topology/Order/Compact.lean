/-
Extracted from Topology/Order/Compact.lean
Genuine: 4 of 11 | Dissolved: 0 | Infrastructure: 7
-/
import Origin.Core

/-!
# Compactness of a closed interval

In this file we prove that a closed interval in a conditionally complete linear ordered type with
order topology (or a product of such types) is compact.

We prove the extreme value theorem (`IsCompact.exists_isMinOn`, `IsCompact.exists_isMaxOn`):
a continuous function on a compact set takes its minimum and maximum values. We provide many
variations of this theorem.

We also prove that the image of a closed interval under a continuous map is a closed interval, see
`ContinuousOn.image_Icc`.

## Tags

compact, extreme value theorem
-/

open Filter OrderDual TopologicalSpace Function Set

open scoped Filter Topology

/-!
### Compactness of a closed interval

In this section we define a typeclass `CompactIccSpace α` saying that all closed intervals in `α`
are compact. Then we provide an instance for a `ConditionallyCompleteLinearOrder` and prove that
the product (both `α × β` and an indexed product) of spaces with this property inherits the
property.

We also prove some simple lemmas about spaces with this property.
-/

class CompactIccSpace (α : Type*) [TopologicalSpace α] [Preorder α] : Prop where
  /-- A closed interval `Set.Icc a b` is a compact set for all `a` and `b`. -/
  isCompact_Icc : ∀ {a b : α}, IsCompact (Icc a b)

export CompactIccSpace (isCompact_Icc)

variable {α : Type*}

lemma CompactIccSpace.mk' [TopologicalSpace α] [Preorder α]
    (h : ∀ {a b : α}, a ≤ b → IsCompact (Icc a b)) : CompactIccSpace α where
  isCompact_Icc {a b} := by_cases h fun hab => by rw [Icc_eq_empty hab]; exact isCompact_empty

lemma CompactIccSpace.mk'' [TopologicalSpace α] [PartialOrder α]
    (h : ∀ {a b : α}, a < b → IsCompact (Icc a b)) : CompactIccSpace α :=
  .mk' fun hab => hab.eq_or_lt.elim (by rintro rfl; simp) h

-- INSTANCE (free from Core): [TopologicalSpace

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): {ι

-- INSTANCE (free from Core): Pi.compact_Icc_space'

-- INSTANCE (free from Core): {α

theorem isCompact_uIcc {α : Type*} [LinearOrder α] [TopologicalSpace α] [CompactIccSpace α]
    {a b : α} : IsCompact (uIcc a b) :=
  isCompact_Icc

-- INSTANCE (free from Core): (priority

variable {α : Type*} [Preorder α] [TopologicalSpace α] [CompactIccSpace α]

-- INSTANCE (free from Core): compactSpace_Icc

end

section openIntervals

variable {α : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α]
