/-
Extracted from Topology/Bornology/Absorbs.lean
Genuine: 3 of 4 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Absorption of sets

Let `M` act on `α`, let `A` and `B` be sets in `α`.
We say that `A` *absorbs* `B` if for sufficiently large `a : M`, we have `B ⊆ a • A`.
Formally, "for sufficiently large `a : M`" means "for all but a bounded set of `a`".

Traditionally, this definition is formulated
for the action of a (semi)normed ring on a module over that ring.

We formulate it in a more general settings for two reasons:

- this way we don't have to depend on metric spaces, normed rings etc;
- some proofs look nicer with this definition than with something like
  `∃ r : ℝ, ∀ a : R, r ≤ ‖a‖ → B ⊆ a • A`.

If `M` is a `GroupWithZero` (e.g., a division ring),
the sets absorbing a given set form a filter, see `Filter.absorbing`.

## Implementation notes

For now, all theorems assume that we deal with (a generalization of) a module over a division ring.
Some lemmas have multiplicative versions for `MulDistribMulAction`s.
They can be added later when someone needs them.

## Keywords

absorbs, absorbent
-/

assert_not_exists Real

open Set Bornology Filter

open scoped Pointwise

section Defs

variable (M : Type*) {α : Type*} [Bornology M] [SMul M α]

def Absorbs (s t : Set α) : Prop :=
  ∀ᶠ a in cobounded M, t ⊆ a • s

def Absorbent (s : Set α) : Prop :=
  ∀ x, Absorbs M s {x}

end Defs

namespace Absorbs

section SMul

variable {M α : Type*} [Bornology M] [SMul M α] {s s₁ s₂ t t₁ t₂ : Set α} {S T : Set (Set α)}

protected lemma empty : Absorbs M s ∅ := by simp [Absorbs]
