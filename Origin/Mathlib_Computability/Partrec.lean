/-
Extracted from Computability/Partrec.lean
Genuine: 5 of 6 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# The partial recursive functions

The partial recursive functions are defined similarly to the primitive
recursive functions, but now all functions are partial, implemented
using the `Part` monad, and there is an additional operation, called
μ-recursion, which performs unbounded minimization: `μ f` returns the
least natural number `n` for which `f n = 0`, or diverges if such `n` doesn't exist.

## Main definitions

- `Nat.Partrec f`: `f` is partial recursive, for functions `f : ℕ →. ℕ`
- `Partrec f`: `f` is partial recursive, for partial functions between `Primcodable` types
- `Computable f`: `f` is partial recursive, for total functions between `Primcodable` types

## References

* [Mario Carneiro, *Formalizing computability theory via partial recursive functions*][carneiro2019]
-/

open List (Vector)

open Encodable Denumerable Part

attribute [-simp] not_forall

namespace Nat

section Rfind

variable (p : ℕ →. Bool)

set_option backward.privateInPublic true in

private def lbp (m n : ℕ) : Prop :=
  m = n + 1 ∧ ∀ k ≤ n, false ∈ p k

set_option backward.privateInPublic true in

private def wf_lbp (H : ∃ n, true ∈ p n ∧ ∀ k < n, (p k).Dom) : WellFounded (lbp p) :=
  ⟨by
    let ⟨n, pn⟩ := H
    suffices ∀ m k, n ≤ k + m → Acc (lbp p) k by exact fun a => this _ _ (Nat.le_add_left _ _)
    intro m k kn
    induction m generalizing k with (refine ⟨_, fun y r => ?_⟩; rcases r with ⟨rfl, a⟩)
    | zero => injection mem_unique pn.1 (a _ kn)
    | succ m IH => exact IH _ (by rw [Nat.add_right_comm]; exact kn)⟩

variable (H : ∃ n, true ∈ p n ∧ ∀ k < n, (p k).Dom)

set_option backward.privateInPublic true in

set_option backward.privateInPublic.warn false in

def rfindX : { n // true ∈ p n ∧ ∀ m < n, false ∈ p m } :=
  suffices ∀ k, (∀ n < k, false ∈ p n) → { n // true ∈ p n ∧ ∀ m < n, false ∈ p m } from
    this 0 fun _ => (Nat.not_lt_zero _).elim
  @WellFounded.fix _ _ (lbp p) (wf_lbp p H)
    (by
      intro m IH al
      have pm : (p m).Dom := by
        rcases H with ⟨n, h₁, h₂⟩
        rcases lt_trichotomy m n with (h₃ | h₃ | h₃)
        · exact h₂ _ h₃
        · rw [h₃]
          exact h₁.fst
        · injection mem_unique h₁ (al _ h₃)
      cases e : (p m).get pm
      · suffices ∀ᵉ k ≤ m, false ∈ p k from IH _ ⟨rfl, this⟩ fun n h => this _ (le_of_lt_succ h)
        intro n h
        rcases h.lt_or_eq_dec with h | h
        · exact al _ h
        · rw [h]
          exact ⟨_, e⟩
      · exact ⟨m, ⟨_, e⟩, al⟩)

end Rfind

def rfind (p : ℕ →. Bool) : Part ℕ :=
  ⟨_, fun h => (rfindX p h).1⟩

theorem rfind_min {p : ℕ →. Bool} {n : ℕ} (h : n ∈ rfind p) : ∀ {m : ℕ}, m < n → false ∈ p m :=
  @(h.snd ▸ @((rfindX p h.fst).2.2))
