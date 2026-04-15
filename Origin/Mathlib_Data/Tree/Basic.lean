/-
Extracted from Data/Tree/Basic.lean
Genuine: 6 of 7 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Binary tree

Provides binary tree storage for values of any type, with O(lg n) retrieval.
See also `Lean.Data.RBTree` for red-black trees - this version allows more operations
to be defined and is better suited for in-kernel computation.

We also specialize for `Tree Unit`, which is a binary tree without any
additional data. We provide the notation `a △ b` for making a `Tree Unit` with children
`a` and `b`.

## References

<https://leanprover-community.github.io/archive/stream/113488-general/topic/tactic.20question.html>
-/

inductive Tree.{u} (α : Type u) : Type u
  | nil : Tree α
  | node : α → Tree α → Tree α → Tree α
  deriving DecidableEq, Repr

compile_inductive% Tree

namespace Tree

universe u

variable {α : Type u}

-- INSTANCE (free from Core): :

def traverse {m : Type* → Type*} [Applicative m] {α β} (f : α → m β) : Tree α → m (Tree β)
  | .nil => pure nil
  | .node a l r => .node <$> f a <*> traverse f l <*> traverse f r

def map {β} (f : α → β) : Tree α → Tree β
  | nil => nil
  | node a l r => node (f a) (map f l) (map f r)

theorem id_map (t : Tree α) : t.map id = t := by
  induction t with
  | nil => rw [map]
  | node v l r hl hr => rw [map, hl, hr, id_eq]

theorem comp_map {β γ : Type*} (f : α → β) (g : β → γ) (t : Tree α) :
    t.map (g ∘ f) = (t.map f).map g := by
  induction t with
  | nil => rw [map, map, map]
  | node v l r hl hr => rw [map, map, map, hl, hr, Function.comp_apply]

theorem traverse_pure (t : Tree α) {m : Type u → Type*} [Applicative m] [LawfulApplicative m] :
    t.traverse (pure : α → m α) = pure t := by
  induction t with
  | nil => rw [traverse]
  | node v l r hl hr =>
    rw [traverse, hl, hr, map_pure, pure_seq, seq_pure, map_pure, map_pure]
