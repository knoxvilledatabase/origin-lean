/-
Extracted from Data/Nat/Find.lean
Genuine: 8 of 8 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# `Nat.find` and `Nat.findGreatest`
-/

variable {m n k : ℕ} {p q : ℕ → Prop}

namespace Nat

section Find

/-! ### `Nat.find` -/

set_option backward.privateInPublic true in

private def lbp (m n : ℕ) : Prop :=
  m = n + 1 ∧ ∀ k ≤ n, ¬p k

variable [DecidablePred p] (H : ∃ n, p n)

set_option backward.privateInPublic true in

private def wf_lbp : WellFounded (@lbp p) :=
  ⟨let ⟨n, pn⟩ := H
    suffices ∀ m k, n ≤ k + m → Acc lbp k from fun _ => this _ _ (Nat.le_add_left _ _)
    fun m =>
    Nat.recOn m
      (fun _ kn =>
        ⟨_, fun y r =>
          match y, r with
          | _, ⟨rfl, a⟩ => absurd pn (a _ kn)⟩)
      fun m IH k kn =>
      ⟨_, fun y r =>
        match y, r with
        | _, ⟨rfl, _a⟩ => IH _ (by rw [Nat.add_right_comm]; exact kn)⟩⟩

set_option backward.privateInPublic true in

set_option backward.privateInPublic.warn false in

protected def findX : { n // p n ∧ ∀ m < n, ¬p m } :=
  @WellFounded.fix _ (fun k => (∀ n < k, ¬p n) → { n // p n ∧ ∀ m < n, ¬p m }) lbp (wf_lbp H)
    (fun m IH al =>
      if pm : p m then ⟨m, pm, al⟩
      else
        have : ∀ n ≤ m, ¬p n := fun n h =>
          Or.elim (Nat.lt_or_eq_of_le h) (al n) fun e => by rw [e]; exact pm
        IH _ ⟨rfl, this⟩ fun n h => this n <| Nat.le_of_succ_le_succ h)
    0 fun _ h => absurd h (Nat.not_lt_zero _)

protected def find : ℕ :=
  (Nat.findX H).1

protected theorem find_spec : p (Nat.find H) :=
  (Nat.findX H).2.left

grind_pattern Nat.find_spec => Nat.find H

protected theorem find_min : ∀ {m : ℕ}, m < Nat.find H → ¬p m :=
  @(Nat.findX H).2.right

protected theorem find_min' {m : ℕ} (h : p m) : Nat.find H ≤ m :=
  Nat.le_of_not_gt fun l => Nat.find_min H l h

lemma find_eq_iff (h : ∃ n : ℕ, p n) : Nat.find h = m ↔ p m ∧ ∀ n < m, ¬p n := by
  constructor
  · grind [Nat.find_min]
  · rintro ⟨hm, hlt⟩
    have := Nat.find_min' h hm
    grind
