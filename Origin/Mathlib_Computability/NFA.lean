/-
Extracted from Computability/NFA.lean
Genuine: 3 of 4 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Nondeterministic Finite Automata

A Nondeterministic Finite Automaton (NFA) is a state machine which
decides membership in a particular `Language`, by following every
possible path that describes an input string.

We show that DFAs and NFAs can decide the same languages, by constructing
an equivalent DFA for every NFA, and vice versa.

As constructing a DFA from an NFA uses an exponential number of states,
we re-prove the pumping lemma instead of lifting `DFA.pumping_lemma`,
in order to obtain the optimal bound on the minimal length of the string.

Like `DFA`, this definition allows for automata with infinite states;
a `Fintype` instance must be supplied for true NFAs.

## Main definitions

* `NFA α σ`: automaton over alphabet `α` and set of states `σ`
* `NFA.evalFrom M S x`: set of possible ending states for an input word `x`
  and set of initial states `S`
* `NFA.accepts M`: the language accepted by the NFA `M`
* `NFA.Path M s t x`: a specific path from `s` to `t` for an input word `x`
* `NFA.Path.supp p`: set of states visited by the path `p`

## Main theorems

* `NFA.pumping_lemma`: every sufficiently long string accepted by the NFA has a substring that can
  be repeated arbitrarily many times (and have the overall string still be accepted)
-/

open Set

open Computability

universe u v

structure NFA (α : Type u) (σ : Type v) where
  /-- The NFA's transition function -/
  step : σ → α → Set σ
  /-- Set of starting states -/
  start : Set σ
  /-- Set of accepting states -/
  accept : Set σ

variable {α : Type u} {σ : Type v} {M : NFA α σ}

namespace NFA

-- INSTANCE (free from Core): :

variable (M) in

def stepSet (S : Set σ) (a : α) : Set σ :=
  ⋃ s ∈ S, M.step s a

theorem mem_stepSet {s : σ} {S : Set σ} {a : α} : s ∈ M.stepSet S a ↔ ∃ t ∈ S, s ∈ M.step t a := by
  simp [stepSet]

variable (M) in
