/-
Extracted from GroupTheory/CommutingProbability.lean
Genuine: 4 of 5 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Commuting Probability
This file introduces the commuting probability of finite groups.

## Main definitions
* `commProb`: The commuting probability of a finite type with a multiplication operation.

## TODO
* Neumann's theorem.
-/

assert_not_exists Ideal TwoSidedIdeal

noncomputable section

open Fintype

variable (M : Type*) [Mul M]

def commProb : ℚ :=
  Nat.card { p : M × M // Commute p.1 p.2 } / (Nat.card M : ℚ) ^ 2

theorem commProb_prod (M' : Type*) [Mul M'] : commProb (M × M') = commProb M * commProb M' := by
  simp_rw [commProb_def, div_mul_div_comm, Nat.card_prod, Nat.cast_mul, mul_pow, ← Nat.cast_mul,
    ← Nat.card_prod, Commute, SemiconjBy, Prod.ext_iff]
  congr 2
  exact Nat.card_congr ⟨fun x => ⟨⟨⟨x.1.1.1, x.1.2.1⟩, x.2.1⟩, ⟨⟨x.1.1.2, x.1.2.2⟩, x.2.2⟩⟩,
    fun x => ⟨⟨⟨x.1.1.1, x.2.1.1⟩, ⟨x.1.1.2, x.2.1.2⟩⟩, ⟨x.1.2, x.2.2⟩⟩, fun x => rfl, fun x => rfl⟩

theorem commProb_pi {α : Type*} (i : α → Type*) [Fintype α] [∀ a, Mul (i a)] :
    commProb (∀ a, i a) = ∏ a, commProb (i a) := by
  simp_rw [commProb_def, Finset.prod_div_distrib, Finset.prod_pow, ← Nat.cast_prod,
    ← Nat.card_pi, Commute, SemiconjBy, funext_iff]
  congr 2
  exact Nat.card_congr ⟨fun x a => ⟨⟨x.1.1 a, x.1.2 a⟩, x.2 a⟩, fun x => ⟨⟨fun a => (x a).1.1,
    fun a => (x a).1.2⟩, fun a => (x a).2⟩, fun x => rfl, fun x => rfl⟩

theorem commProb_function {α β : Type*} [Fintype α] [Mul β] :
    commProb (α → β) = (commProb β) ^ Fintype.card α := by
  rw [commProb_pi, Finset.prod_const, Finset.card_univ]
