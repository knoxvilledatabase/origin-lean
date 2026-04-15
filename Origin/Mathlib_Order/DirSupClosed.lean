/-
Extracted from Order/DirSupClosed.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Sets closed under directed suprema

We say that a set `s` is closed under directed suprema whenever it contains all least upper bounds
for nonempty, directed subsets. Conversely, a set `s` is inaccessible by directed suprema whenever
its complement is closed under directed suprema. Equivalently, if the least upper bound of a
nonempty directed set `t` is contained in `s`, then `t` and `s` must have nonempty intersection.

## Main definitions

- `DirSupClosed`: sets closed under directed suprema.
- `DirSupInacc`: sets inaccessible by directed suprema.
-/

variable {α : Type*} {s t : Set α} {D D₁ D₂ : Set (Set α)}

open Set

section Preorder

variable [Preorder α]

def DirSupClosedOn (D : Set (Set α)) (s : Set α) : Prop :=
  ∀ ⦃d⦄, d ∈ D → d ⊆ s → d.Nonempty → DirectedOn (· ≤ ·) d → ∀ ⦃a⦄, IsLUB d a → a ∈ s

def DirSupInaccOn (D : Set (Set α)) (s : Set α) : Prop :=
  ∀ ⦃d⦄, d ∈ D → d.Nonempty → DirectedOn (· ≤ ·) d → ∀ ⦃a⦄, IsLUB d a → a ∈ s → (d ∩ s).Nonempty

def DirSupClosed (s : Set α) : Prop :=
  ∀ ⦃d⦄, d ⊆ s → d.Nonempty → DirectedOn (· ≤ ·) d → ∀ ⦃a⦄, IsLUB d a → a ∈ s

def DirSupInacc (s : Set α) : Prop :=
  ∀ ⦃d⦄, d.Nonempty → DirectedOn (· ≤ ·) d → ∀ ⦃a⦄, IsLUB d a → a ∈ s → (d ∩ s).Nonempty
