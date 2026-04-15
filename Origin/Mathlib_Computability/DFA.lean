/-
Extracted from Computability/DFA.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Deterministic Finite Automata

A Deterministic Finite Automaton (DFA) is a state machine which
decides membership in a particular `Language`, by following a path
uniquely determined by an input string.

We define regular languages to be ones for which a DFA exists, other formulations
are later proved equivalent.

Note that this definition allows for automata with infinite states,
a `Fintype` instance must be supplied for true DFAs.

## Main definitions

- `DFA α σ`: automaton over alphabet `α` and set of states `σ`
- `M.accepts`: the language accepted by the DFA `M`
- `Language.IsRegular L`: a predicate stating that `L` is a regular language, i.e. there exists
  a DFA that recognizes the language

## Main theorems

- `DFA.pumping_lemma` : every sufficiently long string accepted by the DFA has a substring that can
  be repeated arbitrarily many times (and have the overall string still be accepted)

## Implementation notes

Currently, there are two disjoint sets of simp lemmas: one for `DFA.eval`, and another for
`DFA.evalFrom`. You can switch from the former to the latter using `simp [eval]`.

## TODO

- Should we unify these simp sets, such that `eval` is rewritten to `evalFrom` automatically?
- Should `mem_accepts` and `mem_acceptsFrom` be marked `@[simp]`?
-/

universe u v

open Computability

structure DFA (α : Type u) (σ : Type v) where
  /-- A transition function from state to state labelled by the alphabet. -/
  step : σ → α → σ
  /-- Starting state. -/
  start : σ
  /-- Set of acceptance states. -/
  accept : Set σ

namespace DFA

variable {α : Type u} {σ : Type v} (M : DFA α σ)

-- INSTANCE (free from Core): [Inhabited

def evalFrom (s : σ) : List α → σ :=
  List.foldl M.step s
