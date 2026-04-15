/-
Extracted from Data/Ordmap/Invariants.lean
Genuine: 7 of 7 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Invariants for the verification of `Ordnode`

An `Ordnode`, defined in `Mathlib/Data/Ordmap/Ordnode.lean`, is an inductive type which describes a
tree which stores the `size` at internal nodes.

In this file we define the correctness invariant of an `Ordnode`, comprising:

* `Ordnode.Sized t`: All internal `size` fields must match the actual measured
  size of the tree. (This is not hard to satisfy.)
* `Ordnode.Balanced t`: Unless the tree has the form `()` or `((a) b)` or `(a (b))`
  (that is, nil or a single singleton subtree), the two subtrees must satisfy
  `size l ≤ δ * size r` and `size r ≤ δ * size l`, where `δ := 3` is a global
  parameter of the data structure (and this property must hold recursively at subtrees).
  This is why we say this is a "size balanced tree" data structure.
* `Ordnode.Bounded lo hi t`: The members of the tree must be in strictly increasing order,
  meaning that if `a` is in the left subtree and `b` is the root, then `a ≤ b` and
  `¬(b ≤ a)`. We enforce this using `Ordnode.Bounded` which includes also a global
  upper and lower bound.

This whole file is in the `Ordnode` namespace, because we first have to prove the correctness of
all the operations (and defining what correctness means here is somewhat subtle).
The actual `Ordset` operations are in `Mathlib/Data/Ordmap/Ordset.lean`.

## TODO

This file is incomplete, in the sense that the intent is to have verified
versions and lemmas about all the definitions in `Ordnode.lean`, but at the moment only
a few operations are verified (the hard part should be out of the way, but still).
Contributors are encouraged to pick this up and finish the job, if it appeals to you.

## Tags

ordered map, ordered set, data structure, verified programming
-/

variable {α : Type*}

namespace Ordnode

/-! ### delta and ratio -/

theorem not_le_delta {s} (H : 1 ≤ s) : ¬s ≤ delta * 0 :=
  not_le_of_gt H

theorem delta_lt_false {a b : ℕ} (h₁ : delta * a < b) (h₂ : delta * b < a) : False :=
  not_le_of_gt (lt_trans (mul_lt_mul_of_pos_left h₁ <| by decide) h₂) <| by
    simpa [mul_assoc] using Nat.mul_le_mul_right a (by decide : 1 ≤ delta * delta)

/-! ### `singleton` -/

/-! ### `size` and `empty` -/

def realSize : Ordnode α → ℕ
  | nil => 0
  | node _ l _ r => realSize l + realSize r + 1

/-! ### `Sized` -/

def Sized : Ordnode α → Prop
  | nil => True
  | node s l _ r => s = size l + size r + 1 ∧ Sized l ∧ Sized r

theorem Sized.node' {l x r} (hl : @Sized α l) (hr : Sized r) : Sized (node' l x r) :=
  ⟨rfl, hl, hr⟩

theorem Sized.eq_node' {s l x r} (h : @Sized α (node s l x r)) : node s l x r = .node' l x r := by
  rw [h.1]

theorem Sized.size_eq {s l x r} (H : Sized (@node α s l x r)) :
    size (@node α s l x r) = size l + size r + 1 :=
  H.1
