/-
Extracted from Order/Monotone/Defs.lean
Genuine: 8 of 16 | Dissolved: 0 | Infrastructure: 8
-/
import Origin.Core

/-!
# Monotonicity

This file defines (strictly) monotone/antitone functions. Contrary to standard mathematical usage,
"monotone"/"mono" here means "increasing", not "increasing or decreasing". We use "antitone"/"anti"
to mean "decreasing".

## Definitions

* `Monotone f`: A function `f` between two preorders is monotone if `a ≤ b` implies `f a ≤ f b`.
* `Antitone f`: A function `f` between two preorders is antitone if `a ≤ b` implies `f b ≤ f a`.
* `MonotoneOn f s`: Same as `Monotone f`, but for all `a, b ∈ s`.
* `AntitoneOn f s`: Same as `Antitone f`, but for all `a, b ∈ s`.
* `StrictMono f` : A function `f` between two preorders is strictly monotone if `a < b` implies
  `f a < f b`.
* `StrictAnti f` : A function `f` between two preorders is strictly antitone if `a < b` implies
  `f b < f a`.
* `StrictMonoOn f s`: Same as `StrictMono f`, but for all `a, b ∈ s`.
* `StrictAntiOn f s`: Same as `StrictAnti f`, but for all `a, b ∈ s`.

## Implementation notes

Some of these definitions used to only require `LE α` or `LT α`. The advantage of this is
unclear and it led to slight elaboration issues. Now, everything requires `Preorder α` and seems to
work fine. Related Zulip discussion:
https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Order.20diamond/near/254353352.

## Tags

monotone, strictly monotone, antitone, strictly antitone, increasing, strictly increasing,
decreasing, strictly decreasing
-/

assert_not_exists Nat.instLinearOrder Int.instLinearOrder

open Function

universe u v w

variable {ι : Type*} {α : Type u} {β : Type v} {γ : Type w} {δ : Type*} {π : ι → Type*}

section MonotoneDef

variable [Preorder α] [Preorder β]

def Monotone (f : α → β) : Prop :=
  ∀ ⦃a b⦄, a ≤ b → f a ≤ f b

to_dual_insert_cast Monotone := forall_comm.eq

def Antitone (f : α → β) : Prop :=
  ∀ ⦃a b⦄, a ≤ b → f b ≤ f a

to_dual_insert_cast Antitone := forall_comm.eq

def MonotoneOn (f : α → β) (s : Set α) : Prop :=
  ∀ ⦃a⦄ (_ : a ∈ s) ⦃b⦄ (_ : b ∈ s), a ≤ b → f a ≤ f b

to_dual_insert_cast MonotoneOn := by grind only

def AntitoneOn (f : α → β) (s : Set α) : Prop :=
  ∀ ⦃a⦄ (_ : a ∈ s) ⦃b⦄ (_ : b ∈ s), a ≤ b → f b ≤ f a

to_dual_insert_cast AntitoneOn := by grind only

def StrictMono (f : α → β) : Prop :=
  ∀ ⦃a b⦄, a < b → f a < f b

to_dual_insert_cast StrictMono := forall_comm.eq

def StrictAnti (f : α → β) : Prop :=
  ∀ ⦃a b⦄, a < b → f b < f a

to_dual_insert_cast StrictAnti := forall_comm.eq

def StrictMonoOn (f : α → β) (s : Set α) : Prop :=
  ∀ ⦃a⦄ (_ : a ∈ s) ⦃b⦄ (_ : b ∈ s), a < b → f a < f b

to_dual_insert_cast StrictMonoOn := by grind only

def StrictAntiOn (f : α → β) (s : Set α) : Prop :=
  ∀ ⦃a⦄ (_ : a ∈ s) ⦃b⦄ (_ : b ∈ s), a < b → f b < f a

to_dual_insert_cast StrictAntiOn := by grind only

end MonotoneDef

section Decidable

variable [Preorder α] [Preorder β] {f : α → β} {s : Set α}

-- INSTANCE (free from Core): [i

-- INSTANCE (free from Core): [i

-- INSTANCE (free from Core): [i

-- INSTANCE (free from Core): [i

-- INSTANCE (free from Core): [i

-- INSTANCE (free from Core): [i

-- INSTANCE (free from Core): [i

-- INSTANCE (free from Core): [i

end Decidable

/-! ### Monotonicity in function spaces -/

section Preorder

variable [Preorder α]
