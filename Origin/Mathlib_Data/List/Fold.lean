/-
Extracted from Data/List/Fold.lean
Genuine: 8 of 8 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Bird–Wadler duality of list folds

In their 1988 book _Introduction to Functional Programming_ [birdwadler],
Richard Bird and Philip Wadler stated three duality theorems between `foldl` and `foldr`.
Denoting the combining function as `f`, the theorems are:

1. If `α = β` and `f` is commutative and associative, `l.foldl = l.foldr`
2. If `f` is left-commutative, `l.foldl = l.foldr`
3. `l.reverse.foldl = l.foldr` and `l.reverse.foldr = l.foldl`

Note that `f`'s type differs between Lean's `foldl` (`β → α → β`) and `foldr` (`α → β → β`),
so `flip`s need to be inserted judiciously. For the history behind this type difference
see the appendix to [danvy], which uses a version of `foldl` where `f : α → β → β` to derive
among other things a slight generalisation of the first theorem:

1. If `α = β`, `f` is associative and `a` commutes with all `x : α`, `l.foldl f a = l.foldr f a`

## Main declarations

* `List.foldl_eq_foldr_of_commute`, `List.foldl_eq_foldr`: first duality theorem.
* `List.foldl_flip_eq_foldr`, `List.foldr_flip_eq_foldl`: second duality theorem.

The third duality theorem is in the standard library under the names
`List.foldl_reverse`, `List.foldr_eq_foldl_reverse`,
`List.foldr_reverse` and `List.foldl_eq_foldr_reverse`.
-/

namespace List

variable {α β : Type*} {l : List α} {f : α → β → β} {v : β → α → β} {a : α} {b : β}

lemma foldl_cons_nil : l.foldl (flip cons) [] = l.reverse := by
  induction l <;> simp [flip, foldl_eq_foldr_reverse, -foldr_reverse]

lemma foldl_cons_eq_apply_foldl [hv : RightCommutative v] :
    (a :: l).foldl v b = v (l.foldl v b) a := by
  rw [foldl_cons]
  induction l generalizing a b <;> simp [*, hv.right_comm]

lemma foldr_cons_eq_foldr_apply [hf : LeftCommutative f] :
    (a :: l).foldr f b = l.foldr f (f a b) := by
  rw [foldr_cons]
  induction l generalizing a b <;> simp [*, hf.left_comm]

lemma foldl1_eq_foldr1 {f : α → α → α} [ha : Std.Associative f] {a b : α} :
    f (l.foldl f a) b = f a (l.foldr f b) := by
  induction l generalizing a <;> simp [*, ha.assoc]

theorem foldl_eq_foldr_of_commute {f : α → α → α} [Std.Associative f] (ha : ∀ x, f a x = f x a) :
    l.foldl f a = l.foldr f a := by
  induction l <;> simp [*, foldl_assoc]

theorem foldl_eq_foldr {f : α → α → α} [hf : Std.Commutative f] [Std.Associative f] :
    l.foldl f a = l.foldr f a :=
  foldl_eq_foldr_of_commute (hf.comm a)

theorem foldl_flip_eq_foldr [LeftCommutative f] : l.foldl (flip f) b = l.foldr f b := by
  induction l generalizing b <;> simp [*, flip, foldr_cons_eq_foldr_apply, -foldr_cons]

theorem foldr_flip_eq_foldl [RightCommutative v] : l.foldr (flip v) b = l.foldl v b := by
  induction l generalizing b <;> simp [*, flip, foldl_cons_eq_apply_foldl, -foldl_cons]
