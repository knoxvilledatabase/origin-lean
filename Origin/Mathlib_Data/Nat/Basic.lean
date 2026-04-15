/-
Extracted from Data/Nat/Basic.lean
Genuine: 8 of 14 | Dissolved: 2 | Infrastructure: 4
-/
import Origin.Core

/-!
# Basic operations on the natural numbers

This file builds on `Mathlib/Data/Nat/Init.lean` by adding basic lemmas on natural numbers
depending on Mathlib definitions.

See note [foundational algebra order theory].
-/

assert_not_exists Monoid

open Function

namespace Nat

variable {a b c d m n k : ℕ} {p : ℕ → Prop}

-- INSTANCE (free from Core): instLinearOrder

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): instNontrivial

attribute [gcongr] Nat.succ_le_succ Nat.div_le_div_right Nat.div_le_div

/-! ### `succ`, `pred` -/

lemma succ_injective : Injective Nat.succ := @succ.inj

/-! ### `div` -/

protected theorem div_right_comm (a b c : ℕ) : a / b / c = a / c / b := by
  rw [Nat.div_div_eq_div_mul, Nat.mul_comm, ← Nat.div_div_eq_div_mul]

/-!
### `pow`
-/

-- DISSOLVED: pow_left_injective

protected lemma pow_right_injective (ha : 2 ≤ a) : Injective (a ^ ·) := by
  simp [Injective, le_antisymm_iff, Nat.pow_le_pow_iff_right ha]

-- DISSOLVED: pow_sub_one

/-!
### Recursion and induction principles

This section is here due to dependencies -- the lemmas here require some of the lemmas
proved above, and some of the results in later sections depend on the definitions in this section.
-/

lemma leRecOn_injective {C : ℕ → Sort*} {n m} (hnm : n ≤ m) (next : ∀ {k}, C k → C (k + 1))
    (Hnext : ∀ n, Injective (@next n)) : Injective (@leRecOn C n m hnm next) := by
  induction hnm with
  | refl =>
    intro x y H
    rwa [leRecOn_self, leRecOn_self] at H
  | step hnm ih =>
    intro x y H
    rw [leRecOn_succ hnm, leRecOn_succ hnm] at H
    exact ih (Hnext _ H)

lemma leRecOn_surjective {C : ℕ → Sort*} {n m} (hnm : n ≤ m) (next : ∀ {k}, C k → C (k + 1))
    (Hnext : ∀ n, Surjective (@next n)) : Surjective (@leRecOn C n m hnm next) := by
  induction hnm with
  | refl =>
    intro x
    refine ⟨x, ?_⟩
    rw [leRecOn_self]
  | step hnm ih =>
    intro x
    obtain ⟨w, rfl⟩ := Hnext _ x
    obtain ⟨x, rfl⟩ := ih w
    refine ⟨x, ?_⟩
    rw [leRecOn_succ]

lemma set_induction_bounded {S : Set ℕ} (hk : k ∈ S) (h_ind : ∀ k : ℕ, k ∈ S → k + 1 ∈ S)
    (hnk : k ≤ n) : n ∈ S :=
  @leRecOn (fun n => n ∈ S) k n hnk @h_ind hk

lemma set_induction {S : Set ℕ} (hb : 0 ∈ S) (h_ind : ∀ k : ℕ, k ∈ S → k + 1 ∈ S) (n : ℕ) :
    n ∈ S :=
  set_induction_bounded hb h_ind (zero_le n)

/-! ### `mod`, `dvd` -/

lemma dvd_left_injective : Function.Injective ((· ∣ ·) : ℕ → ℕ → Prop) := fun _ _ h =>
  dvd_right_iff_eq.mp fun a => iff_of_eq (congr_fun h a)
