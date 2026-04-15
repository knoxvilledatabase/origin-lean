/-
Extracted from Data/Tree/Basic.lean
Genuine: 12 | Conflates: 0 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core
import Mathlib.Data.Nat.Notation
import Mathlib.Tactic.TypeStar
import Mathlib.Util.CompileInductive

/-!
# Binary tree

Provides binary tree storage for values of any type, with O(lg n) retrieval.
See also `Lean.Data.RBTree` for red-black trees - this version allows more operations
to be defined and is better suited for in-kernel computation.

We also specialize for `Tree Unit`, which is a binary tree without any
additional data. We provide the notation `a △ b` for making a `Tree Unit` with children
`a` and `b`.

## TODO

Implement a `Traversable` instance for `Tree`.

## References

<https://leanprover-community.github.io/archive/stream/113488-general/topic/tactic.20question.html>
-/

inductive Tree.{u} (α : Type u) : Type u
  | nil : Tree α
  | node : α → Tree α → Tree α → Tree α
  deriving DecidableEq, Repr -- Porting note: Removed `has_reflect`, added `Repr`.

namespace Tree

universe u

variable {α : Type u}

instance : Inhabited (Tree α) :=
  ⟨nil⟩

def map {β} (f : α → β) : Tree α → Tree β
  | nil => nil
  | node a l r => node (f a) (map f l) (map f r)

@[simp]
def numNodes : Tree α → ℕ
  | nil => 0
  | node _ a b => a.numNodes + b.numNodes + 1

@[simp]
def numLeaves : Tree α → ℕ
  | nil => 1
  | node _ a b => a.numLeaves + b.numLeaves

@[simp]
def height : Tree α → ℕ
  | nil => 0
  | node _ a b => max a.height b.height + 1

theorem numLeaves_eq_numNodes_succ (x : Tree α) : x.numLeaves = x.numNodes + 1 := by
  induction x <;> simp [*, Nat.add_comm, Nat.add_assoc, Nat.add_left_comm]

theorem numLeaves_pos (x : Tree α) : 0 < x.numLeaves := by
  rw [numLeaves_eq_numNodes_succ]
  exact x.numNodes.zero_lt_succ

theorem height_le_numNodes : ∀ x : Tree α, x.height ≤ x.numNodes
  | nil => Nat.le_refl _
  | node _ a b => Nat.succ_le_succ <|
    Nat.max_le.2 ⟨Nat.le_trans a.height_le_numNodes <| a.numNodes.le_add_right _,
      Nat.le_trans b.height_le_numNodes <| b.numNodes.le_add_left _⟩

@[simp]
def left : Tree α → Tree α
  | nil => nil
  | node _ l _r => l

@[simp]
def right : Tree α → Tree α
  | nil => nil
  | node _ _l r => r

scoped infixr:65 " △ " => Tree.node ()

compile_inductive% Tree

@[elab_as_elim]
def unitRecOn {motive : Tree Unit → Sort*} (t : Tree Unit) (base : motive nil)
    (ind : ∀ x y, motive x → motive y → motive (x △ y)) : motive t :=
  t.recOn base fun _u ↦ ind

theorem left_node_right_eq_self : ∀ {x : Tree Unit} (_hx : x ≠ nil), x.left △ x.right = x
  | nil, h => by trivial
  | node _ _ _, _ => rfl  -- Porting note: `a △ b` no longer works in pattern matching

end Tree
