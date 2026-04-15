/-
Extracted from Tactic/Group.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FailIfNoProgress
import Mathlib.Algebra.Group.Commutator

/-!
# `group` tactic

Normalizes expressions in the language of groups. The basic idea is to use the simplifier
to put everything into a product of group powers (`zpow` which takes a group element and an
integer), then simplify the exponents using the `ring` tactic. The process needs to be repeated
since `ring` can normalize an exponent to zero, leading to a factor that can be removed
before collecting exponents again. The simplifier step also uses some extra lemmas to avoid
some `ring` invocations.

## Tags

group_theory
-/

namespace Mathlib.Tactic.Group

open Lean

open Lean.Meta

open Lean.Parser.Tactic

open Lean.Elab.Tactic

@[to_additive]
theorem zpow_trick {G : Type*} [Group G] (a b : G) (n m : ℤ) :
    a * b ^ n * b ^ m = a * b ^ (n + m) := by rw [mul_assoc, ← zpow_add]

@[to_additive]
theorem zpow_trick_one {G : Type*} [Group G] (a b : G) (m : ℤ) :
    a * b * b ^ m = a * b ^ (m + 1) := by rw [mul_assoc, mul_self_zpow]

@[to_additive]
theorem zpow_trick_one' {G : Type*} [Group G] (a b : G) (n : ℤ) :
    a * b ^ n * b = a * b ^ (n + 1) := by rw [mul_assoc, mul_zpow_self]

syntax (name := aux_group₁) "aux_group₁" (location)? : tactic

macro_rules

| `(tactic| aux_group₁ $[at $location]?) =>

  `(tactic| simp -decide -failIfUnchanged only

    [commutatorElement_def, mul_one, one_mul,

      ← zpow_neg_one, ← zpow_natCast, ← zpow_mul,

      Int.ofNat_add, Int.ofNat_mul,

      Int.mul_neg, Int.neg_mul, neg_neg,

      one_zpow, zpow_zero, zpow_one, mul_zpow_neg_one,

      ← mul_assoc,

      ← zpow_add, ← zpow_add_one, ← zpow_one_add, zpow_trick, zpow_trick_one, zpow_trick_one',

      tsub_self, sub_self, add_neg_cancel, neg_add_cancel]

  $[at $location]?)

syntax (name := aux_group₂) "aux_group₂" (location)? : tactic

macro_rules

| `(tactic| aux_group₂ $[at $location]?) =>

  `(tactic| ring_nf $[at $location]?)

syntax (name := group) "group" (location)? : tactic

macro_rules

| `(tactic| group $[$loc]?) =>

  `(tactic| repeat (fail_if_no_progress (aux_group₁ $[$loc]? <;> aux_group₂ $[$loc]?)))

end Mathlib.Tactic.Group
