/-
Extracted from NumberTheory/RamificationInertia/Ramification.lean
Genuine: 5 of 5 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Ramification index

Given `P : Ideal S` lying over `p : Ideal R` for the ring extension `f : R →+* S`
(assuming `P` and `p` are prime or maximal where needed),
the **ramification index** `Ideal.ramificationIdx p P` is the multiplicity of `P` in `map f p`.

## Implementation notes

Often the above theory is set up in the case where:
* `R` is the ring of integers of a number field `K`,
* `L` is a finite separable extension of `K`,
* `S` is the integral closure of `R` in `L`,
* `p` and `P` are maximal ideals,
* `P` is an ideal lying over `p`.

We will try to relax the above hypotheses as much as possible.

## Notation

In this file, `e` stands for the ramification index of `P` over `p`, leaving `p` and `P` implicit.

-/

namespace Ideal

universe u v

variable {R : Type u} [CommRing R]

variable {S : Type v} [CommRing S] [Algebra R S]

variable (p : Ideal R) (P : Ideal S)

local notation "f" => algebraMap R S

open Module

open UniqueFactorizationMonoid

attribute [local instance] Ideal.Quotient.field

section DecEq

noncomputable def ramificationIdx : ℕ := sSup {n | map f p ≤ P ^ n}

variable {p P}

theorem ramificationIdx_eq_find [DecidablePred fun n ↦ ∀ (k : ℕ), map f p ≤ P ^ k → k ≤ n]
    (h : ∃ n, ∀ k, map f p ≤ P ^ k → k ≤ n) :
    ramificationIdx p P = Nat.find h := by
  convert Nat.sSup_def h

theorem ramificationIdx_eq_zero (h : ∀ n : ℕ, ∃ k, map f p ≤ P ^ k ∧ n < k) :
    ramificationIdx p P = 0 :=
  dif_neg (by push Not; exact h)

theorem ramificationIdx_spec {n : ℕ} (hle : map f p ≤ P ^ n) (hgt : ¬map f p ≤ P ^ (n + 1)) :
    ramificationIdx p P = n := by
  classical
  let Q : ℕ → Prop := fun m => ∀ k : ℕ, map f p ≤ P ^ k → k ≤ m
  have : Q n := by
    intro k hk
    refine le_of_not_gt fun hnk => ?_
    exact hgt (hk.trans (Ideal.pow_le_pow_right hnk))
  rw [ramificationIdx_eq_find ⟨n, this⟩]
  refine le_antisymm (Nat.find_min' _ this) (le_of_not_gt fun h : Nat.find _ < n => ?_)
  obtain this' := Nat.find_spec ⟨n, this⟩
  exact h.not_ge (this' _ hle)

theorem ramificationIdx_lt {n : ℕ} (hgt : ¬map f p ≤ P ^ n) : ramificationIdx p P < n := by
  classical
  rcases n with - | n
  · simp at hgt
  · rw [Nat.lt_succ_iff]
    have : ∀ k, map f p ≤ P ^ k → k ≤ n := by
      refine fun k hk => le_of_not_gt fun hnk => ?_
      exact hgt (hk.trans (Ideal.pow_le_pow_right hnk))
    rw [ramificationIdx_eq_find ⟨n, this⟩]
    exact Nat.find_min' ⟨n, this⟩ this
